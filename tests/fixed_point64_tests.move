#[test_only]
module fixed_point64::fixed_point64_tests {
    use fixed_point64::fixed_point64;

    const MAX_U64: u64 = 18446744073709551615; // 2^64 - 1
    const MAX_U128: u128 = 340282366920938463463374607431768211455;
    const TWO_POWER_64: u128 = 18446744073709551616;

    #[test]
    fun test_is_zero() {
        let zero = fixed_point64::encode(0);
        assert!(fixed_point64::is_zero(&zero), 0);

        let non_zero = fixed_point64::encode(1);
        assert!(!fixed_point64::is_zero(&non_zero), 1);
    }

    #[test]
    fun test_compare() {
        assert!(fixed_point64::compare(&fixed_point64::encode(100), &fixed_point64::encode(100)) == 0, 0);
        assert!(fixed_point64::compare(&fixed_point64::encode(200), &fixed_point64::encode(100)) == 2, 1);
        assert!(fixed_point64::compare(&fixed_point64::encode(100), &fixed_point64::encode(200)) == 1, 1);
    }

    #[test]
    fun test_encode_decode() {
        let a = fixed_point64::encode(100);
        let b = fixed_point64::decode(a);
        let c = fixed_point64::decode_round_up(a);
        let d = fixed_point64::decode_round_down(a);
        assert!(b == 100, 0);
        assert!(c == 100, 0);
        assert!(d == 100, 0);

        a = fixed_point64::encode(MAX_U64);
        b = fixed_point64::decode(a);
        c = fixed_point64::decode_round_up(a);
        d = fixed_point64::decode_round_down(a);
        assert!(b == MAX_U64, 1);
        assert!(c == MAX_U64, 1);
        assert!(d == MAX_U64, 1);

        a = fixed_point64::encode(0);
        b = fixed_point64::decode(a);
        c = fixed_point64::decode_round_up(a);
        d = fixed_point64::decode_round_down(a);
        assert!(b == 0, 2);
        assert!(c == 0, 2);
        assert!(d == 0, 2);

        a = fixed_point64::fraction(1, 2);
        b = fixed_point64::decode(a);
        c = fixed_point64::decode_round_up(a);
        d = fixed_point64::decode_round_down(a);
        assert!(b == 1, 3);
        assert!(c == 1, 3);
        assert!(d == 0, 3);
        
        a = fixed_point64::fraction(2, 2);
        b = fixed_point64::decode(a);
        c = fixed_point64::decode_round_up(a);
        d = fixed_point64::decode_round_down(a);
        assert!(b == 1, 4);
        assert!(c == 1, 4);
        assert!(d == 1, 4);
        
        a = fixed_point64::fraction(2, 3);
        b = fixed_point64::decode(a);
        c = fixed_point64::decode_round_up(a);
        d = fixed_point64::decode_round_down(a);
        assert!(b == 1, 5);
        assert!(c == 1, 5);
        assert!(d == 0, 5);
    }

    #[test]
    fun test_one() {
        let a = fixed_point64::one();
        assert!(fixed_point64::to_u128(a) == 1 << 64, 0);
    }

    #[test]
    fun test_zero() {
        let a = fixed_point64::zero();
        assert!(fixed_point64::to_u128(a) == 0, 0);
    }
    
    #[test]
    fun test_from_and_to() {
        let a = fixed_point64::from_u128(1);
        let b = fixed_point64::to_u128(a);
        assert!(b == 1, 0);
    }

    #[test]
    fun test_mul() {
        let a = fixed_point64::encode(5);
        let z = fixed_point64::mul(a, 2);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64 * 10, 0);
        assert!(fixed_point64::decode(z) == 10, 1);
    }

    #[test]
    #[expected_failure]
    fun test_fail_mul_u128_large() {
        let a = fixed_point64::encode(5);
        fixed_point64::mul_u128(a, MAX_U128);
    }

    #[test]
    fun test_fraction() {
        let a = fixed_point64::fraction(8, 2);
        assert!(fixed_point64::to_u128(a) == TWO_POWER_64 * 4, 0);
        assert!(fixed_point64::decode(a) == 4, 1);
    }

    #[test]
    fun test_fraction_large() {
        let a = fixed_point64::fraction_u128(MAX_U128, MAX_U128 - 1);
        assert!(fixed_point64::to_u128(a) == TWO_POWER_64, 0);
        assert!(fixed_point64::decode(a) == 1, 1);
    }

    #[test]
    fun test_fraction_mul() {
        let a = fixed_point64::fraction(5, 4); // 1.25
        let z = fixed_point64::mul(a, 2); // 2.5
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64 * 5 / 2, 0);
        assert!(fixed_point64::decode(z) == 3, 1);
    }

    #[test]
    #[expected_failure(abort_code = fixed_point64::fixed_point64::ERR_DIVIDE_BY_ZERO)]
    fun test_fail_fraction() {
        let a = fixed_point64::fraction(256, 0);
        fixed_point64::to_u128(a);
    }

    #[test]
    fun test_div() {
        let a = fixed_point64::encode(8);
        let z = fixed_point64::div(a, 2);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64 * 4, 0);
        assert!(fixed_point64::decode(z) == 4, 1);
    }

    #[test]
    #[expected_failure(abort_code = fixed_point64::fixed_point64::ERR_DIVIDE_BY_ZERO)]
    fun test_fail_div() {
        let a = fixed_point64::encode(1);
        fixed_point64::div(a, 0);
    }

    #[test]
    fun test_add() {
        let a = fixed_point64::encode(2);
        let z = fixed_point64::add(a, 3);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64 * 5, 0);
        assert!(fixed_point64::decode(z) == 5, 1);
    }

    #[test]
    fun test_mul_div() {
        let a = fixed_point64::encode(10);
        let z = fixed_point64::mul_div_u128(a, 2, 5);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64 * 4, 0);
        assert!(fixed_point64::decode(z) == 4, 1);
    }

    #[test]
    #[expected_failure]
    fun test_fail_overflow_add() {
        let a = fixed_point64::encode(MAX_U64);
        fixed_point64::add(a, MAX_U64);
    }

    #[test]
    #[expected_failure]
    fun test_fail_overflow_add_u128() {
        let a = fixed_point64::encode(1);
        fixed_point64::add_u128(a, MAX_U128 - 100);
    }

    #[test]
    fun test_sub() {
        let a = fixed_point64::encode(3);
        let z = fixed_point64::sub(a, 2);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64, 0);
        assert!(fixed_point64::decode(z) == 1, 1);
    }
    
    #[test]
    #[expected_failure]
    fun test_fail_underflow_sub() {
        let a = fixed_point64::encode(5);
        fixed_point64::sub(a, 10);
    }

    #[test]
    #[expected_failure]
    fun test_fail_underflow_sub_fp_large() {
        let a = fixed_point64::encode(MAX_U64);
        fixed_point64::sub_u128(a, MAX_U128 - 100);
    }

    #[test]
    fun test_add_fp() {
        let a = fixed_point64::encode(2);
        let b = fixed_point64::encode(3);
        let z = fixed_point64::add_fp(a, b);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64 * 5, 0);
        assert!(fixed_point64::decode(z) == 5, 1);
    }
    
    #[test]
    #[expected_failure]
    fun test_fail_overflow_add_fp() {
        let a = fixed_point64::encode(MAX_U64);
        let b = fixed_point64::encode(3);
        fixed_point64::add_fp(a, b);
    }

    #[test]
    fun test_sub_fp() {
        let a = fixed_point64::encode(3);
        let b = fixed_point64::encode(2);
        let z = fixed_point64::sub_fp(a, b);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64, 0);
        assert!(fixed_point64::decode(z) == 1, 1);
    }
    
    #[test]
    #[expected_failure]
    fun test_fail_underflow_sub_fp() {
        let a = fixed_point64::encode(5);
        let b = fixed_point64::encode(10);
        fixed_point64::sub_fp(a, b);
    }

    #[test]
    fun test_mul_fp() {
        let a = fixed_point64::encode(3);
        let b = fixed_point64::encode(2);
        let z = fixed_point64::mul_fp(a, b);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64 * 6, 0);
        assert!(fixed_point64::decode(z) == 6, 1);
    }
    
    #[test]
    fun test_mul_fp_fraction() {
        let a = fixed_point64::fraction(5, 4); // 1.25
        let b = fixed_point64::encode(2);
        let z = fixed_point64::mul_fp(a, b);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64 * 5 / 2, 0);
        assert!(fixed_point64::decode(z) == 3, 1);
    }

    #[test]
    fun test_mul_fp_precision() {
        let a = fixed_point64::from_u128(20724119864554512384); // 1.123456789
        let b = fixed_point64::from_u128(55112494640199483392); // 2.987654321
        let z = fixed_point64::mul_fp(a, b);
        // expected: 3.35650053011
        assert!(fixed_point64::to_u128(z) == 61916506262258222549, 0); // 3.35650053011
    }

    #[test]
    fun test_mul_fp_precision_2() {
        let a = fixed_point64::from_u128(409161529984780471035); // 22.180690985349592381
        let b = fixed_point64::from_u128(1844582179910627); // 0.000099995000339357
        let z = fixed_point64::mul_fp(a, b);
        // expected: 0.002217958202607205
        assert!(fixed_point64::to_u128(z) == 40914107329680144, 0); // 0.0022179582
    }
    
    #[test]
    #[expected_failure]
    fun test_fail_overflow_mul_fp() {
        let a = fixed_point64::encode(MAX_U64);
        let b = fixed_point64::encode(10);
        fixed_point64::mul_fp(a, b);
    }
    
    #[test]
    fun test_div_fp() {
        let a = fixed_point64::encode(6);
        let b = fixed_point64::encode(2);
        let z = fixed_point64::div_fp(a, b);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64 * 3, 0);
        assert!(fixed_point64::decode(z) == 3, 1);
    }
    
    #[test]
    fun test_div_fp_fraction() {
        let a = fixed_point64::fraction(5, 4); // 1.25
        let b = fixed_point64::fraction(1, 4); // 0.25
        let z = fixed_point64::div_fp(a, b);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64 * 5, 0);
        assert!(fixed_point64::decode(z) == 5, 1);
    }

    #[test]
    fun test_div_fp_precision() {
        let a = fixed_point64::from_u128(409161529984780471035);
        let b = fixed_point64::from_u128(1844582179910627);
        let z = fixed_point64::div_fp(a, b);
        assert!(fixed_point64::to_u128(z) == 4091819876955756114341262, 0); // 221818
    }

    #[test]
    fun test_div_fp_fraction_precision() {
        let z = fixed_point64::fraction(7, 13); // 0.5384615384615384
        assert!(fixed_point64::to_u128(z) == 9932862193535912408, 0); // 0.53846153846
    }

    #[test]
    fun test_mul_div_fp() {
        let a = fixed_point64::encode(10);
        let b = fixed_point64::encode(2);
        let c = fixed_point64::encode(5);
        let z = fixed_point64::mul_div_fp(a, b, c);
        assert!(fixed_point64::to_u128(z) == TWO_POWER_64 * 4, 0);
        assert!(fixed_point64::decode(z) == 4, 1);
    }
    
    #[test]
    #[expected_failure(abort_code = fixed_point64::fixed_point64::ERR_DIVIDE_RESULT_TOO_LARGE)]
    fun test_fail_divisor_too_small_div_fp() {
        let a = fixed_point64::encode(10);
        let b = fixed_point64::from_u128(1);
        fixed_point64::div_fp(a, b);
    }
    
    #[test]
    #[expected_failure(abort_code = fixed_point64::fixed_point64::ERR_DIVIDE_RESULT_TOO_LARGE)]
    fun test_fail_overflow_div_fp() {
        let a = fixed_point64::from_u128(1 << 125);
        let b = fixed_point64::from_u128(1 << 35);
        fixed_point64::div_fp(a, b);
    }
    
    #[test]
    fun test_min_max() {
        let a = fixed_point64::encode(6);
        let b = fixed_point64::encode(2);
        assert!(fixed_point64::min(&a, &b) == &b, 0);
        assert!(fixed_point64::max(&a, &b) == &a, 1);
    }
    
    #[test]
    fun test_lt_lte_gt_gte_eq() {
        let a = fixed_point64::from_u128(1);
        let b = fixed_point64::from_u128(2);

        assert!(fixed_point64::lt(&a, &b), 0);
        assert!(fixed_point64::lte(&a, &b), 0);
        assert!(fixed_point64::lte(&a, &a), 0);
        assert!(fixed_point64::gt(&b, &a), 0);
        assert!(fixed_point64::gte(&b, &a), 0);
        assert!(fixed_point64::gte(&b, &b), 0);

        assert!(!fixed_point64::lt(&b, &a), 0);
        assert!(!fixed_point64::lte(&b, &a), 0);
        assert!(!fixed_point64::gt(&a, &b), 0);
        assert!(!fixed_point64::gte(&a, &b), 0);

        assert!(!fixed_point64::eq(&a, &b), 0);
        let c = fixed_point64::from_u128(1);
        assert!(fixed_point64::eq(&a, &c), 0);
    }
}