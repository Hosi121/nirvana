const CLASSES: [u64; 32] = [
    3, 0, 7, 2, 5, 1, 6, 4, 1, 7, 2, 6, 0, 5, 4, 3, 6, 2, 4, 0, 7, 3, 1, 5, 4, 5, 0, 1, 3, 6, 2, 7,
];

pub(crate) fn inputs() -> Vec<[u64; 4]> {
    let mut inputs = Vec::new();
    for key in 0..64u64 {
        inputs.push([key, 17 ^ (key << 58), u64::MAX - 23 + key / 8, key / 8]);
    }
    for key in [
        0,
        1,
        7,
        8,
        15,
        31,
        32,
        63,
        64,
        u64::MAX,
        u64::MAX - 1,
        u64::MAX - 7,
        0x7fff_ffff,
        0x8000_0000,
        1 << 32,
        1 << 63,
    ] {
        inputs.push([key, u64::MAX, 0x1234_5678_9abc_def0, 0x8765_4321_1234_5678]);
    }
    let mut seed = 0x89bd_37a1_c125_ef23u64;
    for _ in 0..64 {
        inputs.push(std::array::from_fn(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        }));
    }
    inputs
}

pub(crate) fn oracle(name: &str, mut r: [u64; 4]) -> Vec<u64> {
    let (a, b, d) = (r[1], r[2], r[3]);
    match name {
        "modular-pipeline" => {
            let (mut value, mut salt) = (a, b);
            for i in 0..(d & 3) + 1 {
                let mut stage = r[0].wrapping_add(i) & 3;
                if stage == 3 {
                    stage = (value ^ salt) % 3;
                }
                value = match stage {
                    0 => value.wrapping_add(salt.wrapping_mul(3)),
                    1 => value.rotate_left(9) ^ salt,
                    _ => (value ^ salt).wrapping_mul(0x100000001b3),
                };
                salt = salt.wrapping_add(value & 255);
            }
            r[1] = value;
            r[2] = salt;
        }
        "mapped-switch" => {
            let key = CLASSES[((r[0] ^ d) & 31) as usize];
            r[1] = match key {
                0 => a.wrapping_add(b.wrapping_mul(3)),
                1 => a.rotate_left(9),
                2 => a ^ b.wrapping_add(d),
                3 => a.wrapping_sub(d.wrapping_mul(5)),
                4 => (a ^ b).wrapping_mul(7),
                5 => a.wrapping_add(b & 1023),
                6 => (a >> 11) | (b << 53),
                _ => (a | b) ^ d,
            };
            r[2] = b.wrapping_add(key);
        }
        "state-machine" | "permuted-machine" => {
            let mut phase = r[0] & 7;
            let (mut value, mut total) = (a, b);
            for _ in 0..(d & 7) + 1 {
                if name == "permuted-machine" {
                    value = value.swap_bytes();
                }
                let next = match phase {
                    0 => {
                        value = value.wrapping_add(total);
                        3
                    }
                    1 => {
                        total ^= value;
                        6
                    }
                    2 => {
                        value = value.rotate_left(5);
                        7
                    }
                    3 => {
                        value = value.wrapping_mul(3);
                        1
                    }
                    4 => {
                        total = total.wrapping_add(value ^ 0xa5);
                        0
                    }
                    5 => {
                        value = value.wrapping_sub(total);
                        2
                    }
                    6 => {
                        total = total.rotate_right(7);
                        5
                    }
                    _ => {
                        value ^= total.wrapping_add(17);
                        4
                    }
                };
                phase = if name == "permuted-machine" {
                    (phase + (value & 7) + 1) & 7
                } else {
                    next ^ (value & 3)
                };
            }
            r[0] = phase;
            r[1] = value;
            r[2] = total;
        }
        "reused-selector" => {
            let first = match r[0] & 7 {
                0 => a.wrapping_add(b),
                1 => a.wrapping_mul(5),
                2 => a ^ d,
                3 => a.rotate_left(7),
                4 => a.wrapping_sub(b),
                5 => a.wrapping_add(b & 255),
                6 => a | d,
                _ => a & b,
            };
            let second = (first ^ b) & 7;
            r[1] = match second {
                0 => first.wrapping_add(11),
                1 => first ^ 0x55,
                2 => first.wrapping_mul(9),
                3 => first.rotate_right(3),
                4 => first.wrapping_sub(d),
                5 => first | b,
                6 => first & d,
                _ => first ^ b,
            };
            r[2] = second;
        }
        _ => panic!("unknown fixture {name}"),
    }
    let value = match name {
        "mapped-switch" => r[1] ^ r[2] ^ r[3],
        "state-machine" | "permuted-machine" => r[1] ^ r[2] ^ r[0],
        _ => r[1] ^ r[2],
    };
    let mut result = vec![value];
    result.extend(r);
    result
}
