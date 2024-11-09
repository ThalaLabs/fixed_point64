/// Implementation of FixedPoint u64 in Move language.
module fixed_point64::fixed_point64 {
    // Error codes.

    /// When divide by zero attempted.
    const ERR_DIVIDE_BY_ZERO: u64 = 0;

    /// When divisor is too small that will cause overflow
    const ERR_DIVISOR_TOO_SMALL: u64 = 1;
    
    /// When divide result is too large that will cause overflow
    const ERR_DIVIDE_RESULT_TOO_LARGE: u64 = 2;

    /// When multiply result is too large that it will cause overflow
    const ERR_MULTIPLY_RESULT_TOO_LARGE: u64 = 3;

    /// 2^64 == 1 << 64
    const TWO_POW_64: u128 = 1 << 64;

    /// 2^32 == 1 << 32
    const TWO_POW_32: u128 = 1 << 32;

    /// When a and b are equals.
    const EQUAL: u8 = 0;

    /// When a is less than b equals.
    const LESS_THAN: u8 = 1;

    /// When a is greater than b.
    const GREATER_THAN: u8 = 2;

    const MAX_U128: u256 = 340282366920938463463374607431768211455;

    /// The resource to store `FixedPoint64`.
    struct FixedPoint64 has copy, store, drop {
        v: u128
    }

    /// Encode `u64` to `FixedPoint64`
    public fun encode(x: u64): FixedPoint64 {
        let v = (x as u128) << 64;
        FixedPoint64{ v }
    }

    /// Decode a `FixedPoint64` into a `u64` by rounding to nearest integer
    /// This should be the default way to convert back to integer
    /// Unless you have a good reason to round up or down
    public fun decode(fp: FixedPoint64): u64 {
        let a = ((fp.v >> 64) as u64);
        let v_shifted = fp.v >> 63;
        // equivalent to (we want to avoid using `&`)
        // if (fp.v & mask > 0) a = a + 1;
        if (v_shifted % 2 == 1) {
            a + 1
        }
        else {
            a
        }
    }
    
    /// Decode a `FixedPoint64` into a `u64` by rounding down
    public fun decode_round_down(fp: FixedPoint64): u64 {
        let a = ((fp.v >> 64) as u64);
        a
    }

    /// Decode a `FixedPoint64` into a `u64` by rounding up
    public fun decode_round_up(fp: FixedPoint64): u64 {
        let a = ((fp.v >> 64) as u64);
        if (fp.v - (fp.v / TWO_POW_64) * TWO_POW_64 > 0) {
            a + 1
        }
        else {
            a
        }
    }

    /// Get `u128` (raw value) from FixedPoint64
    public fun to_u128(fp: FixedPoint64): u128 {
        fp.v
    }
    
    /// Convert from `u128` (raw value) to FixedPoint64
    public fun from_u128(v: u128): FixedPoint64 {
        FixedPoint64{ v }
    }

    /// Get integer "one" in FixedPoint64
    public fun one(): FixedPoint64 {
        FixedPoint64{ v: TWO_POW_64 }
    }
    
    /// Get integer "zero" in FixedPoint64
    public fun zero(): FixedPoint64 {
        FixedPoint64{ v: 0 }
    }

    /// Multiply a `FixedPoint64` by a `u128`, returning a `FixedPoint64`
    public fun mul(fp: FixedPoint64, y: u128): FixedPoint64 {
        // vm would direct abort when overflow occured
        let v = fp.v * y;

        FixedPoint64{ v }
    }

    /// Divide a `FixedPoint64` by a `u128`, returning a `FixedPoint64`.
    public fun div(fp: FixedPoint64, y: u128): FixedPoint64 {
        assert!(y != 0, ERR_DIVIDE_BY_ZERO);

        let v = fp.v / y;
        FixedPoint64{ v }
    }

    /// Multiply a `FixedPoint64` by a `u128` and then divide by another `u128`, returning a `u128`
    public fun mul_div(fp: FixedPoint64, y: u128, z: u128): FixedPoint64 {
        assert!(z != 0, ERR_DIVIDE_BY_ZERO);
        let v = (((fp.v as u256) * (y as u256) / (z as u256)) as u128);

        FixedPoint64{ v }
    }

    /// Add a `FixedPoint64` and a `u128`, returning a `FixedPoint64`
    public fun add(fp: FixedPoint64, y: u128): FixedPoint64 {
        // vm would direct abort when overflow occured
        let v = ((fp.v as u256) + ((y as u256) << 64) as u128);

        FixedPoint64{ v }
    }

    /// Subtract `FixedPoint64` by a `u128`, returning a `FixedPoint64`
    public fun sub(fp: FixedPoint64, y: u128): FixedPoint64 {
        // vm would direct abort when underflow occured
        let v = ((fp.v as u256) - ((y as u256) << 64) as u128);

        FixedPoint64{ v }
    }
    spec sub {
        aborts_if fp.v < (y << 64);
    }

    /// Add a `FixedPoint64` and a `FixedPoint64`, returning a `FixedPoint64`
    public fun add_fp(a: FixedPoint64, b: FixedPoint64): FixedPoint64 {
        // vm would direct abort when overflow occured
        let v = a.v + b.v;

        FixedPoint64{ v }
    }

    /// Subtract `FixedPoint64` by a `FixedPoint64`, returning a `FixedPoint64`
    public fun sub_fp(a: FixedPoint64, b: FixedPoint64): FixedPoint64 {
        // vm would direct abort when underflow occured
        let v = a.v - b.v;

        FixedPoint64{ v }
    }
    spec sub_fp {
        aborts_if a.v < b.v;
    }

    /// Multiply a `FixedPoint64` by a `FixedPoint64`, returning a `FixedPoint64`
    /// To avoid overflow, the result must be smaller than MAX_U64
    public fun mul_fp(a: FixedPoint64, b: FixedPoint64): FixedPoint64 {
        // Cast to u256 to avoid overflow during multiplication
        let a_u256 = (a.v as u256);
        let b_u256 = (b.v as u256);

        // Perform full precision multiplication
        let result_u256 = a_u256 * b_u256;

        // Adjust the scale: divide by 2^64 to bring back to FixedPoint64 scale
        let scaled_result = result_u256 >> 64;

        // Ensure the result fits into u128
        assert!(scaled_result <= MAX_U128, ERR_MULTIPLY_RESULT_TOO_LARGE);

        let v = (scaled_result as u128);

        FixedPoint64{ v }
    }
    
    /// Divide a `FixedPoint64` by a `FixedPoint64`, returning a `FixedPoint64`.
    /// To avoid overflow, the result must be smaller than MAX_U128
    public fun div_fp(a: FixedPoint64, b: FixedPoint64): FixedPoint64 {
        // Ensure denominator is not zero
        assert!(b.v != 0, ERR_DIVISOR_TOO_SMALL);

        // Cast a and b to u256 for higher precision
        let a_u256 = (a.v as u256);
        let b_u256 = (b.v as u256);

        // Scale the numerator by 2^64 to preserve precision
        let scaled_a = a_u256 << 64;

        assert!(scaled_a >= 0, ERR_DIVIDE_RESULT_TOO_LARGE);

        // Perform the division with full precision
        let result_u256 = scaled_a / b_u256;

        // Ensure the result fits into u128
        assert!(result_u256 <= MAX_U128, ERR_DIVIDE_RESULT_TOO_LARGE);

        let v = (result_u256 as u128);

        FixedPoint64{ v }
    }

    /// Perform a mul_div of a `FixedPoint64` by a `FixedPoint64` and then divide by another `FixedPoint64`, returning a `FixedPoint64`.
    public fun mul_div_fp(a: FixedPoint64, b: FixedPoint64, c: FixedPoint64): FixedPoint64 {
        assert!(c.v != 0, ERR_DIVIDE_BY_ZERO);

        // Cast to u256 to avoid overflow during multiplication
        let a_u256 = (a.v as u256);
        let b_u256 = (b.v as u256);
        let c_u256 = (c.v as u256);

        // Perform the mul_div with full precision
        // No scale adjustment necessary: multiplication shifts right 64, division left 64, net 0 shift needed
        let result_u256 = a_u256 * b_u256 / c_u256;

        // Ensure the result fits into u128
        assert!(result_u256 <= MAX_U128, ERR_DIVIDE_RESULT_TOO_LARGE);

        let v = (result_u256 as u128);

        FixedPoint64{ v }
    }

    /// Returns a `FixedPoint64` which represents the ratio of the numerator to the denominator.
    public fun fraction(numerator: u128, denominator: u128): FixedPoint64 {
        assert!(denominator != 0, ERR_DIVIDE_BY_ZERO);

        let r = (numerator as u256) << 64;
        let v = (r / (denominator as u256) as u128);

        FixedPoint64{ v }
    }
    spec fraction {
        aborts_if denominator == 0 with ERR_DIVIDE_BY_ZERO;
        ensures result.v == (numerator << 64) / denominator;
    }

    /// Compare two `FixedPoint64` numbers.
    public fun compare(left: &FixedPoint64, right: &FixedPoint64): u8 {
        if (left.v == right.v) {
            return EQUAL
        } else if (left.v < right.v) {
            return LESS_THAN
        } else {
            return GREATER_THAN
        }
    }
    spec compare {
        ensures left.v == right.v ==> result == EQUAL;
        ensures left.v < right.v ==> result == LESS_THAN;
        ensures left.v > right.v ==> result == GREATER_THAN;
    }

    /// Less than
    public fun lt(left: &FixedPoint64, right: &FixedPoint64): bool {
        compare(left, right) == LESS_THAN
    }

    /// Greater than
    public fun gt(left: &FixedPoint64, right: &FixedPoint64): bool {
        compare(left, right) == GREATER_THAN
    }

    /// Less or equal than
    public fun lte(left: &FixedPoint64, right: &FixedPoint64): bool {
        compare(left, right) != GREATER_THAN
    }

    /// Greater or equal than
    public fun gte(left: &FixedPoint64, right: &FixedPoint64): bool {
        compare(left, right) != LESS_THAN
    }

    /// Equal than
    public fun eq(left: &FixedPoint64, right: &FixedPoint64): bool {
        left.v == right.v
    }

    /// Check if `FixedPoint64` is zero
    public fun is_zero(fp: &FixedPoint64): bool {
        fp.v == 0
    }
    spec is_zero {
        ensures fp.v == 0 ==> result == true;
        ensures fp.v > 0 ==> result == false;
    }

    public fun min(a: &FixedPoint64, b: &FixedPoint64): &FixedPoint64 {
        if (compare(a, b) == LESS_THAN) a else b
    }
    
    public fun max(a: &FixedPoint64, b: &FixedPoint64): &FixedPoint64 {
        if (compare(a, b) == GREATER_THAN) a else b
    }
}
