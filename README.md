## FixedPoint64

Implements fixed point numbers in Move language using the Q number format.

Use u128 as underlying data storage. High 64 bits for integer part, Low 64 bits for fractional part.

Similar one used in [Uniswap](https://github.com/Uniswap/v2-core/blob/master/contracts/libraries/UQ112x112.sol) v2 core.

## Compile

    aptos move compile

## Test

    aptos move test

## Usage

- `encode(x: u64): FixedPoint64`: Convert u64 integer to FP64

- `decode(fp: FixedPoint64): u64`: Convert FP64 to u64 integer by rounding down (truncating the fractional part). 
    - Examples: 2.00 -> 2, 2.01 -> 2, 2.99 -> 2
    - This is the default way to convert to integer.

- `decode_round_up(fp: FixedPoint64): u64`: Convert FP64 to u64 integer by rounding up. 
    - Examples: 2.00 -> 2, 2.01 -> 3, 2.99 -> 3
    - Be careful when using this. You should not mint more coins than the receipient entitles

- `to_u128(fp: FixedPoint64): u128`: Get the raw u128 value of FP64
    - The result is NOT the actual integer value

- `from_u128(v: u128): FixedPoint64`: Create FP64 from raw u128 value
    - The input is NOT the actual integer value


## Add as dependency

Add to `Move.toml`:

```toml
[dependencies.FixedPoint64]
git = "https://github.com/ThalaLabs/fixed_point64.git"
rev = "<commit hash>"
```

And then use in code:

```move
use fixed_point64::fixed_point64;
...
let number = fixed_point64::encode(10);
```

## LICENSE

MIT.
