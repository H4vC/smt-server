#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(script) = std::str::from_utf8(data) {
        let config = qfbvsmtrs::Config::default().with_budget(Some(std::time::Duration::from_millis(25)));
        let _ = qfbvsmtrs::parse_smt2(script);
        let _ = qfbvsmtrs::solve_smt2(script, &config);
    }
});
