use std::{ops::{Add, Neg, Sub}, fmt::Display, cmp::Ordering};

const BASE: u8 = 10;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BigInt {
    /** 
     * The sign of negative.
     * `false` if the number is bigger or equals to zero,
     * `true` if the number is less than zero.
     */
    negative: bool,

    /**
     * The numbers storage by a vector.
     * e.g. If the number means 123, this field will just like `vec![1, 2, 3]`.
     */
    numbers: Vec<u8>
}

impl BigInt {
    /**
     * Returns a zero, which `negative` is `false` and `numbers` is `vec![0]`.
     */
    pub fn zero() -> Self {
        BigInt { negative: false, numbers: Vec::from([0]) }
    }

    /**
     * Returns the absolute value of the number.
     */
    pub fn abs(&self) -> Self {
        if !self.negative { self.to_owned() } else {
            BigInt { negative: !self.negative, ..self.to_owned() }
        }
    }
}

impl TryFrom<&str> for BigInt {
    type Error = ParseError;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let mut negative = false;
        let mut numbers = vec![];

        for c in s.chars() {
            /* The first char is '-' means it's a negative number */
            if c == '-' {
                negative = true;
                continue;
            }
            numbers.push(prase_char(c)?)
        }
        /* Remove the meaningless zero */
        loop {
            if numbers[0] != 0 {
                break;
            }
            numbers.remove(0);
        }
        Ok(Self { negative, numbers })
    }
} 

#[test]
fn test_create() {
    let nonnegative = BigInt::try_from("114").unwrap();
    println!("{}", nonnegative);

    let negative = BigInt::try_from("-514").unwrap();
    println!("{}", negative);

    let with_zero = BigInt::try_from("0001230").unwrap();
    println!("{}", with_zero);
}

impl Display for BigInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        if self.negative {
            s += "-";
        }
        for n in &self.numbers {
            s += &n.to_string();
        }
        write!(f, "{}", s)
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[test]
fn test_partial_orb() {
    let big = BigInt::try_from("12345").unwrap();
    let small = BigInt::try_from("1234").unwrap();
    assert!(big > small);
}

impl Ord for BigInt {
    fn cmp(&self, other: &Self) -> Ordering {
        /* Left is nonnegative and right is negative should be greater */
        if !self.negative && other.negative {
            return Ordering::Greater;
        }

        /* Left is negative and right is nonnegative should be less */
        if self.negative && !other.negative {
            return Ordering::Less;
        }

        let left_len = self.numbers.len();
        let right_len = other.numbers.len();

        /* Both are nonnegative */
        if !self.negative && !other.negative {
            if left_len != right_len {
                return left_len.cmp(&right_len);
            }
        }

        /* Both are negative */
        if self.negative && other.negative {
            if left_len != right_len {
                return right_len.cmp(&left_len);
            }
        }

        /* Compare by numbers if the length are same */
        assert_eq!(left_len, right_len);
        if !self.negative && !other.negative {
            for k in 0..left_len {
                if self.numbers[k] != other.numbers[k] {
                    return self.numbers.cmp(&other.numbers);
                }
            }
        }
        if self.negative && other.negative {
            for k in 0..left_len {
                if self.numbers[k] != other.numbers[k] {
                    return other.numbers.cmp(&self.numbers);
                }
            }
        }

        Ordering::Equal
    }
}

#[test]
fn test_cmp() {
    /* Same length (both are nonnegative) */
    let greater = BigInt::try_from("2").unwrap();
    let less = BigInt::try_from("1").unwrap();
    println!("{:?}", greater.cmp(&less));   /* Greater */
    println!("{:?}", less.cmp(&greater));   /* Less */

    /* Same number */
    let num = BigInt::try_from("1").unwrap();
    let eq = BigInt::try_from("1").unwrap();
    println!("{:?}", num.cmp(&eq)); /* Equals */
    println!("{:?}", eq.cmp(&num)); /* Equals */

    /* Same length but different sign */
    let nonnegative = BigInt::try_from("1").unwrap();
    let negative = BigInt::try_from("-1").unwrap();
    println!("{:?}", nonnegative.cmp(&negative));   /* Greater */
    println!("{:?}", negative.cmp(&greater));       /* Less */

    /* Different length (both are nonnegative) */
    let big = BigInt::try_from("20").unwrap();
    let small = BigInt::try_from("1").unwrap();
    println!("{:?}", big.cmp(&small));  /* Greater */
    println!("{:?}", small.cmp(&big));  /* Less */

    /* Different length (both are negative) */
    let big = BigInt::try_from("-1").unwrap();
    let small = BigInt::try_from("-20").unwrap();
    println!("{:?}", big.cmp(&small));  /* Greater */
    println!("{:?}", small.cmp(&big));  /* Less */

    /* Same length (both are negative) */
    let greater = BigInt::try_from("-1").unwrap();
    let less = BigInt::try_from("-2").unwrap();
    println!("{:?}", greater.cmp(&less));   /* Greater */
    println!("{:?}", less.cmp(&greater));   /* Less */
}

impl Neg for BigInt {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let new_sign = !self.negative;
        BigInt { negative: new_sign, numbers: self.numbers }
    }
}

#[test]
fn test_neg() {
    let big_int = BigInt::try_from("114514").unwrap();
    println!("{}", -big_int);
}

impl Add for BigInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        fn add_numbers(left: Vec<u8>, right: Vec<u8>) -> Vec<u8> {
            let (left, right, bigger_len) = balance_len(left, right);

            let mut carry_bit = 0;
            let mut sum = Vec::with_capacity(bigger_len);

            for k in 0..bigger_len {
                sum.push((left[k] + right[k] + carry_bit) % BASE);
                carry_bit = (left[k] + right[k] + carry_bit) / BASE;
            }
            sum
        }

        match (self.negative, rhs.negative) {
            (false, false) => {
                let numbers = add_numbers(self.numbers, rhs.numbers);
                BigInt { negative: false, numbers }
            },
            (false, true) => {
                self - rhs.abs()
            },
            (true, false) => {
                -(self.abs() - rhs)
            },
            (true, true) => {
                -(self.abs() + rhs.abs())
            }
        }
    }
}

#[test]
fn test_add() {
    let left = BigInt::try_from("114000").unwrap();
    let right = BigInt::try_from("514").unwrap();
    println!("{}", left + right);

    let left = BigInt::try_from("114514").unwrap();
    let right = BigInt::try_from("-514").unwrap();
    println!("{}", left + right);
}

impl Sub for BigInt {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        fn sub_numbers(left: Vec<u8>, right: Vec<u8>) -> Vec<u8> {
            let (mut left, mut right, bigger_len) = balance_len(left, right);
            let mut results = Vec::with_capacity(bigger_len);

            left.reverse();
            right.reverse();

            for k in 0..bigger_len {
                if left[k] < right[k] {
                    left[k + 1] -= 1;
                    left[k] += BASE;
                }
                results.push(left[k] - right[k]);
            }
            
            results.reverse();
            results
        }

        match (self.negative, rhs.negative) {
            (false, true) => {
                self + rhs.abs()
            },
            (true, true) => {
                -(self.abs() + rhs.abs())
            },
            (true, false) => {
                -(self.abs() + rhs.abs())
            },
            (false, false) => {
                if self.abs() >= rhs.abs() {
                    let numbers = sub_numbers(self.numbers, rhs.numbers);
                    let negative = false;
                    BigInt { negative, numbers }
                }
                else {
                    let numbers = sub_numbers(rhs.numbers, self.numbers);
                    let negative = true;
                    BigInt { negative, numbers }
                }
            }
        }
    }
}

#[test]
fn test_sub() {
    /* Same number */
    let eq = BigInt::try_from("1").unwrap();
    let same = BigInt::try_from("1").unwrap();
    println!("{}", eq - same);

    /* Both are nonnegative */
    let big = BigInt::try_from("10").unwrap();
    let small = BigInt::try_from("2").unwrap();
    println!("{}", big.clone() - small.clone());
    println!("{}", small - big);

    /* Both are negative */
    let big = BigInt::try_from("-3").unwrap();
    let small = BigInt::try_from("-50").unwrap();
    println!("{}", big.clone() - small.clone());
    println!("{}", small - big);

    println!("{}", BigInt::try_from("114514").unwrap() - BigInt::try_from("514").unwrap())
}

fn prase_char(c: char) -> Result<u8, ParseError> {
    match c {
        '0' => Ok(0),
        '1' => Ok(1),
        '2' => Ok(2),
        '3' => Ok(3),
        '4' => Ok(4),
        '5' => Ok(5),
        '6' => Ok(6),
        '7' => Ok(7),
        '8' => Ok(8),
        '9' => Ok(9),
        other => Err(ParseError { exceptional_char: other })
    }
}

fn fill_zero(origin: Vec<u8>, len: usize) -> Vec<u8> {
    if origin.len() >= len {
        return origin;
    }
    let mut clone = origin.clone();
    clone.reverse();
    let mut new = Vec::with_capacity(len);
    let mut index = 0;
    loop {
        if index >= len {
            break;
        }
        match clone.get(index) {
            Some(n) => new.push(n.to_owned()),
            None => new.push(0),
        }
        index += 1;
    }
    new.reverse();
    new
}

fn balance_len(left: Vec<u8>, right: Vec<u8>) -> (Vec<u8>, Vec<u8>, usize) {
    if left.len() > right.len() {
        let bigger_len = left.len();
        let right = fill_zero(right, bigger_len);
        (left, right, bigger_len)
    }
    else {
        let bigger_len = right.len();
        let left = fill_zero(left, bigger_len);
        (left, right, bigger_len)
    }
}

#[derive(Debug)]
pub struct ParseError { pub exceptional_char: char }

#[macro_export]
macro_rules! big_int {
    ($num_str: literal) => {
        BigInt::try_from($num_str).unwrap()
    };
}

#[test]
fn test_macro() {
    let big_int = big_int!("1234567890") + big_int!("114514");
    println!("{}", big_int);
}