/-! # MD5

The MD5 sum of a file, as TeX computes it (`\file_mdfive_hash:n`, pdfTeX's
`\pdfmdfivesum`): `leanify.sty` compares the sum of the article it typesets with the sum
of the article that Leanify checked, to say when the marks and the summary of the status
file are those of an earlier version of the article. (It identifies a version; nothing
rests on it.) -/

namespace Leanify.Md5

def K : Array UInt32 := #[
    0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

def S : Array UInt32 := #[7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- The message with its padding: `0x80`, zeros, and the length in bits (64 bits, little-endian). -/
def pad (m : ByteArray) : ByteArray := Id.run do
  let mut out := m.push 0x80
  while out.size % 64 != 56 do out := out.push 0
  let bits : UInt64 := m.size.toUInt64 * 8
  for i in [0:8] do out := out.push ((bits >>> (8 * i.toUInt64)).toUInt8)
  pure out

def word (m : ByteArray) (i : Nat) : UInt32 :=
  (m.get! i).toUInt32 ||| ((m.get! (i + 1)).toUInt32 <<< 8) ||| ((m.get! (i + 2)).toUInt32 <<< 16) |||
    ((m.get! (i + 3)).toUInt32 <<< 24)

/-- The four words of the sum. -/
def sum (m : ByteArray) : UInt32 × UInt32 × UInt32 × UInt32 := Id.run do
  let p := pad m
  let mut a0 : UInt32 := 0x67452301
  let mut b0 : UInt32 := 0xefcdab89
  let mut c0 : UInt32 := 0x98badcfe
  let mut d0 : UInt32 := 0x10325476
  for blk in [0:p.size / 64] do
    let mut a := a0
    let mut b := b0
    let mut c := c0
    let mut d := d0
    for i in [0:64] do
      let (f, g) : UInt32 × Nat :=
        if i < 16 then ((b &&& c) ||| ((~~~b) &&& d), i)
        else if i < 32 then ((d &&& b) ||| ((~~~d) &&& c), (5 * i + 1) % 16)
        else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
        else (c ^^^ (b ||| (~~~d)), (7 * i) % 16)
      let f' := f + a + K[i]! + word p (blk * 64 + 4 * g)
      a := d
      d := c
      c := b
      b := b + rotl f' S[i]!
    a0 := a0 + a
    b0 := b0 + b
    c0 := c0 + c
    d0 := d0 + d
  pure (a0, b0, c0, d0)

/-- The sum as 32 hexadecimal digits (lower case). -/
def hex (m : ByteArray) : String :=
  let (a, b, c, d) := sum m
  let digit (n : UInt32) : Char := "0123456789abcdef".toList.getD n.toNat '0'
  let byte (x : UInt32) (k : UInt32) : List Char :=
    let v := (x >>> (8 * k)) &&& 0xff
    [digit (v >>> 4), digit (v &&& 0xf)]
  String.ofList ([a, b, c, d].flatMap fun x => [0, 1, 2, 3].flatMap (byte x))

end Leanify.Md5
