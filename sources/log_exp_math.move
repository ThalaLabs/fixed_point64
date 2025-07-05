module fixed_point64::log_exp_math {
    use fixed_point64::fixed_point64::{Self, FixedPoint64};

    // Error codes.

    /// When exponent is too large
    const ERR_EXPONENT_TOO_LARGE: u64 = 0;
    const ERR_LOG_EXP_MATH_DIVIDE_BY_ZERO: u64 = 1;

    const ONE_HALF_RAW: u128 = 1 << 63;
    const ONE_RAW: u128 = 1 << 64;
    const TWO_RAW: u128 = 1 << 65;
    const TWO_POW_2_RAW: u128 = 1 << 66;
    const TWO_POW_3_RAW: u128 = 1 << 67;
    const TWO_POW_4_RAW: u128 = 1 << 68;
    const TWO_POW_5_RAW: u128 = 1 << 69;
    const TWO_POW_6_RAW: u128 = 1 << 70;
    const TWO_POW_NEG_1_RAW: u128 = 1 << 63;
    const TWO_POW_NEG_2_RAW: u128 = 1 << 62;
    const TWO_POW_NEG_3_RAW: u128 = 1 << 61;
    const TWO_POW_NEG_4_RAW: u128 = 1 << 60;

    const EXP_1_RAW: u128 = 50143449209799256682;
    const EXP_2_RAW: u128 = 136304026803256390412;
    const EXP_4_RAW: u128 = 1007158100559408451354;
    const EXP_8_RAW: u128 = 54988969081439155412736;
    const EXP_16_RAW: u128 = 163919806582506698591828152;
    const EXP_32_RAW: u128 = 1456609517792428406714055862390917;
    const EXP_1_OVER_2_RAW: u128 = 30413539329486470295;
    const EXP_1_OVER_4_RAW: u128 = 23686088245777032822;
    const EXP_1_OVER_8_RAW: u128 = 20902899511243624348;
    const EXP_1_OVER_16_RAW: u128 = 19636456851539679189;

    const LOG_2_E_INV_RAW: u128 = 12786308645202655659; // log_e_2 == ln(2)

    const ONE_PLUS_TEN_EXP_MINUS_9: u128 = 18446744092156295689; // fixed_point64::fraction(1000000001, 1000000000)
    const ONE_MINUS_TEN_EXP_MINUS_9: u128 = 18446744055262807542; // fixed_point64::fraction(999999999, 1000000000)

    const PRECISION: u8 = 64; // number of bits in the mantissa

    // code reference: https://github.com/dmoulding/log2fix/blob/master/log2fix.c
    // algorithm: http://www.claysturner.com/dsp/BinaryLogarithm.pdf
    public fun log2(x: FixedPoint64): (u8, FixedPoint64) {
        let z = fixed_point64::to_u128(x);
        let y: u128 = 0;
        let y_negative: u128 = 0;
        let b: u128 = 1 << (PRECISION - 1);
        let i: u8 = 0;
        let sign: u8 = 1;

        // normalize input to the range [1,2)
        while (z >= TWO_RAW) {
            z = z >> 1;
            y = y + ONE_RAW;
        };

        while (z < ONE_RAW) {
            sign = 0;
            z = z << 1;
            y_negative = y_negative + ONE_RAW;
        };

        while (i < 62) {
            // to calculate (z*z) >> 64, use the fact that z is in the range [1,2)
            // (z >> 1) can fill in lower 64 bits of u128
            // therefore, (z >> 1) * (z >> 1) will not overflow
            z = ((z >> 1) * (z >> 1)) >> 62;
            if (z >= TWO_RAW) { 
                z = z >> 1;
                y = y + b;
            };
            b = b >> 1;
            i = i + 1;
        };

        let result = if (sign > 0) { fixed_point64::from_u128(y) } else { fixed_point64::from_u128(y_negative - y) };

        (sign, result)
    }

    public fun ln(x: FixedPoint64): (u8, FixedPoint64) {
        // ln(x) = log_2(x) / log_2(e)
        let (sign, result) = log2(x);
        result = fixed_point64::mul_fp(result, fixed_point64::from_u128(LOG_2_E_INV_RAW));
        (sign, result)
    }

    public fun exp(sign: u8, x: FixedPoint64): FixedPoint64 {
        assert!(fixed_point64::to_u128(x) < TWO_POW_6_RAW, ERR_EXPONENT_TOO_LARGE);
        let result;
        if (fixed_point64::to_u128(x) == 0) {
            result = fixed_point64::one();
        } else if (sign == 0) {
            result = fixed_point64::div_fp(fixed_point64::one(), exp(1, x));
        } else if (fixed_point64::to_u128(x) == ONE_RAW) {
            result = fixed_point64::from_u128(EXP_1_RAW);
        } else {
            result = fixed_point64::one();
            
            if (fixed_point64::to_u128(x) >= TWO_POW_5_RAW) {
                x = fixed_point64::sub_fp(x, fixed_point64::from_u128(TWO_POW_5_RAW));
                result = fixed_point64::mul_fp(result, fixed_point64::from_u128(EXP_32_RAW));
            };
            if (fixed_point64::to_u128(x) >= TWO_POW_4_RAW) {
                x = fixed_point64::sub_fp(x, fixed_point64::from_u128(TWO_POW_4_RAW));
                result = fixed_point64::mul_fp(result, fixed_point64::from_u128(EXP_16_RAW));
            };
            if (fixed_point64::to_u128(x) >= TWO_POW_3_RAW) {
                x = fixed_point64::sub_fp(x, fixed_point64::from_u128(TWO_POW_3_RAW));
                result = fixed_point64::mul_fp(result, fixed_point64::from_u128(EXP_8_RAW));
            };
            if (fixed_point64::to_u128(x) >= TWO_POW_2_RAW) {
                x = fixed_point64::sub_fp(x, fixed_point64::from_u128(TWO_POW_2_RAW));
                result = fixed_point64::mul_fp(result, fixed_point64::from_u128(EXP_4_RAW));
            };
            if (fixed_point64::to_u128(x) >= TWO_RAW) {
                x = fixed_point64::sub_fp(x, fixed_point64::from_u128(TWO_RAW));
                result = fixed_point64::mul_fp(result, fixed_point64::from_u128(EXP_2_RAW));
            };
            if (fixed_point64::to_u128(x) >= ONE_RAW) {
                x = fixed_point64::sub_fp(x, fixed_point64::from_u128(ONE_RAW));
                result = fixed_point64::mul_fp(result, fixed_point64::from_u128(EXP_1_RAW));
            };
            if (fixed_point64::to_u128(x) >= TWO_POW_NEG_1_RAW) {
                x = fixed_point64::sub_fp(x, fixed_point64::from_u128(TWO_POW_NEG_1_RAW));
                result = fixed_point64::mul_fp(result, fixed_point64::from_u128(EXP_1_OVER_2_RAW));
            };
            if (fixed_point64::to_u128(x) >= TWO_POW_NEG_2_RAW) {
                x = fixed_point64::sub_fp(x, fixed_point64::from_u128(TWO_POW_NEG_2_RAW));
                result = fixed_point64::mul_fp(result, fixed_point64::from_u128(EXP_1_OVER_4_RAW));
            };
            if (fixed_point64::to_u128(x) >= TWO_POW_NEG_3_RAW) {
                x = fixed_point64::sub_fp(x, fixed_point64::from_u128(TWO_POW_NEG_3_RAW));
                result = fixed_point64::mul_fp(result, fixed_point64::from_u128(EXP_1_OVER_8_RAW));
            };
            if (fixed_point64::to_u128(x) >= TWO_POW_NEG_4_RAW) {
                x = fixed_point64::sub_fp(x, fixed_point64::from_u128(TWO_POW_NEG_4_RAW));
                result = fixed_point64::mul_fp(result, fixed_point64::from_u128(EXP_1_OVER_16_RAW));
            };

            // now, x is in the range [0, e^{1/16})
            // if x is 0, we can directly return
            // otherwise, use Taylor series expansion for e^x: 1 + x + (x^2 / 2!) + (x^3 / 3!) + ... + (x^n / n!).

            if (fixed_point64::to_u128(x) != 0) {
                let term = x;
                let series_sum = fixed_point64::one();
                series_sum = fixed_point64::add_fp(series_sum, term);

                term = fixed_point64::div(fixed_point64::mul_fp(term, x), 2);
                series_sum = fixed_point64::add_fp(series_sum, term);

                term = fixed_point64::div(fixed_point64::mul_fp(term, x), 3);
                series_sum = fixed_point64::add_fp(series_sum, term);

                term = fixed_point64::div(fixed_point64::mul_fp(term, x), 4);
                series_sum = fixed_point64::add_fp(series_sum, term);

                term = fixed_point64::div(fixed_point64::mul_fp(term, x), 5);
                series_sum = fixed_point64::add_fp(series_sum, term);

                term = fixed_point64::div(fixed_point64::mul_fp(term, x), 6);
                series_sum = fixed_point64::add_fp(series_sum, term);

                term = fixed_point64::div(fixed_point64::mul_fp(term, x), 7);
                series_sum = fixed_point64::add_fp(series_sum, term);

                term = fixed_point64::div(fixed_point64::mul_fp(term, x), 8);
                series_sum = fixed_point64::add_fp(series_sum, term);

                result = fixed_point64::mul_fp(result, series_sum);
            };
        };
        result
    }

    spec exp {
        // opaque is required for recursive function
        // otherwise move prover will complain even if we don't prove anything here
        pragma opaque;
    }

    public fun pow(x: FixedPoint64, y: FixedPoint64): FixedPoint64 {
        let (success, result) = try_simple_pow(x, y);
        if (success) {
            result
        } else {
            pow_internal(x, y)
        }
    }
    
    /// pow_up multiplies pow result by (1 + 10^-9) if numerical approximation is used in pow
    /// based on experiments, the result is always greater than or equal to the true value
    public fun pow_up(x: FixedPoint64, y: FixedPoint64): FixedPoint64 {
        let (success, result) = try_simple_pow(x, y);
        if (success) {
            result
        } else {
            fixed_point64::mul_fp(pow_internal(x, y), fixed_point64::from_u128(ONE_PLUS_TEN_EXP_MINUS_9))
        }
    }
    
    /// pow_down multiplies pow result by (1 - 10^-9) if numerical approximation is used in pow
    /// based on experiments, the result is always smaller than or equal to the true value
    public fun pow_down(x: FixedPoint64, y: FixedPoint64): FixedPoint64 {
        let (success, result) = try_simple_pow(x, y);
        if (success) {
            result
        } else {
            fixed_point64::mul_fp(pow_internal(x, y), fixed_point64::from_u128(ONE_MINUS_TEN_EXP_MINUS_9))
        }
    }

    /// try_simple_pow returns the result of pow if it can be computed using simple rules
    /// e.g. x^0 = 1, x^1 = x, x^2 = x * x, x^4 = x^2 * x^2
    /// returns (true, value) if the result can be computed
    /// returns (false, 0) if the result cannot be computed
    fun try_simple_pow(x: FixedPoint64, y: FixedPoint64): (bool, FixedPoint64) {
        if (fixed_point64::to_u128(y) == 0) {
            // We solve the 0^0 indetermination by making it equal to one.
            (true, fixed_point64::one())
        } else if (fixed_point64::to_u128(x) == 0) {
            (true, fixed_point64::zero())
        } else if (fixed_point64::to_u128(y) == ONE_RAW) {
            (true, x)
        } else if (fixed_point64::to_u128(y) == TWO_RAW) {
            (true, fixed_point64::mul_fp(x, x))
        } else if (fixed_point64::to_u128(y) == TWO_POW_2_RAW) {
            let x_squared = fixed_point64::mul_fp(x, x);
            (true, fixed_point64::mul_fp(x_squared, x_squared))
        } else if (fixed_point64::to_u128(y) == ONE_HALF_RAW) {
            let x_u256 = (fixed_point64::to_u128(x) as u256);
            let x_scaled = x_u256 << 64;
            let sqrt = sqrt(x_scaled);

            (true, fixed_point64::from_u128((sqrt as u128)))
        } else {
            (false, fixed_point64::zero())
        }
    }

    // formula: x^y = exp(y * ln(x))
    // this function does not check validity of x and y. Caller should ensure handling of special cases such as x = 0 or y = 0
    fun pow_internal(x: FixedPoint64, y: FixedPoint64): FixedPoint64 {
        let (sign, ln_x) = ln(x);
        let y_times_ln_x = fixed_point64::mul_fp(y, ln_x);
        exp(sign, y_times_ln_x)
    }

    /// Returns square root of x, precisely floor(sqrt(x))
    /// Adapted from math128: https://github.com/aptos-labs/aptos-core/blob/main/aptos-move/framework/aptos-stdlib/sources/math128.move#L143
    public fun sqrt(x: u256): u256 {
        if (x == 0) return 0;
        // Note the plus 1 in the expression. Let n = floor_lg2(x) we have x in [2^n, 2^{n+1}) and thus the answer in
        // the half-open interval [2^(n/2), 2^{(n+1)/2}). For even n we can write this as [2^(n/2), sqrt(2) 2^{n/2})
        // for odd n [2^((n+1)/2)/sqrt(2), 2^((n+1)/2). For even n the left end point is integer for odd the right
        // end point is integer. If we choose as our first approximation the integer end point we have as maximum
        // relative error either (sqrt(2) - 1) or (1 - 1/sqrt(2)) both are smaller then 1/2.
        let res = 1 << ((floor_log2(x) + 1) >> 1);
        // We use standard newton-rhapson iteration to improve the initial approximation.
        // The error term evolves as delta_i+1 = delta_i^2 / 2 (quadratic convergence).
        // It turns out that after 5 iterations the delta is smaller than 2^-64 and thus below the treshold.
        res = (res + x / res) >> 1;
        res = (res + x / res) >> 1;
        res = (res + x / res) >> 1;
        res = (res + x / res) >> 1;
        res = (res + x / res) >> 1;
        // We add one additional iteration for the u256 sqrt implementation to improve approximation
        res = (res + x / res) >> 1;
        min(res, x / res)
    }

    /// Returns floor(log2(x))
    /// Adapted from math128: https://github.com/aptos-labs/aptos-core/blob/main/aptos-move/framework/aptos-stdlib/sources/math128.move#L81
    public fun floor_log2(x: u256): u8 {
        let res = 0;
        assert!(x != 0, ERR_LOG_EXP_MATH_DIVIDE_BY_ZERO);
        // Effectively the position of the most significant set bit
        let n = 128;
        while (n > 0) {
            if (x >= (1 << n)) {
                x = x >> n;
                res = res + n;
            };
            n = n >> 1;
        };
        res
    }

    /// Return the smallest of two numbers.
    /// Adapted from math128: https://github.com/aptos-labs/aptos-core/blob/main/aptos-move/framework/aptos-stdlib/sources/math128.move#L18
    public fun min(a: u256, b: u256): u256 {
        if (a < b) a else b
    }
}
