pub mod trie;

use aho_corasick::AhoCorasick;
use aho_corasick::AhoCorasickBuilder;
use aho_corasick::MatchKind;
use data_encoding::Encoding;
use data_encoding::BASE64;
use data_encoding::HEXLOWER;
use data_encoding::HEXUPPER;
use itertools::Itertools;
use num_bigint::BigUint;
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use once_cell::sync::Lazy;
use regex::bytes::Regex;
use regex::bytes::RegexSet;
use serde::Deserialize;
use serde::Serialize;
use std::cmp::min;
use std::cmp::Reverse;
use std::collections::VecDeque;
use std::fmt::Write as FmtWrite;
use std::io::Write as IoWrite;
use std::iter::once;
use std::str;
use std::str::from_utf8_unchecked;
use trie::Trie;

fn decode_uuid(e: &Encoding, raw: &[u8]) -> [u8; 16] {
  let mut out = [0u8; 16];
  e.decode_mut(&raw[0..8], &mut out[0..4]).unwrap();
  e.decode_mut(&raw[9..13], &mut out[4..6]).unwrap();
  e.decode_mut(&raw[14..18], &mut out[6..8]).unwrap();
  e.decode_mut(&raw[19..23], &mut out[8..10]).unwrap();
  e.decode_mut(&raw[24..36], &mut out[10..16]).unwrap();
  out
}

fn encode_uuid(e: &Encoding, raw: &[u8], out: &mut Vec<u8>) {
  out.extend_from_slice(e.encode(&raw[0..4]).as_bytes());
  out.push(b'-');
  out.extend_from_slice(e.encode(&raw[4..6]).as_bytes());
  out.push(b'-');
  out.extend_from_slice(e.encode(&raw[6..8]).as_bytes());
  out.push(b'-');
  out.extend_from_slice(e.encode(&raw[8..10]).as_bytes());
  out.push(b'-');
  out.extend_from_slice(e.encode(&raw[10..16]).as_bytes());
}

struct BufByteReader<'a>(&'a [u8]);
impl<'a> BufByteReader<'a> {
  pub fn read(&mut self) -> u8 {
    let c = self.0[0];
    self.0 = &self.0[1..];
    c
  }

  pub fn read_many(&mut self, n: usize) -> &[u8] {
    let s = &self.0[..n];
    self.0 = &self.0[n..];
    s
  }

  pub fn at_end(&self) -> bool {
    self.0.is_empty()
  }
}

struct VarU56;

impl VarU56 {
  fn compress_value(uncompressed: u64, compressed: &mut Vec<u8>) {
    let mut int = uncompressed;
    // WARNING: We must at least write one byte.
    loop {
      let mut rem = u8::try_from(int % 128).unwrap();
      int /= 128;
      if int != 0 {
        rem |= 128;
      };
      compressed.push(rem);
      if int == 0 {
        break;
      };
    }
  }

  fn compress(uncompressed: &str, compressed: &mut Vec<u8>) {
    let int = u64::from_str_radix(uncompressed, 10).unwrap();
    Self::compress_value(int, compressed);
  }

  fn decompress_as_value(compressed: &mut BufByteReader) -> u64 {
    let mut v = 0u64;
    for i in 0.. {
      let c = compressed.read();
      v |= u64::from(c & 127) * (128 * i);
      if c & 128 == 0 {
        break;
      };
    }
    v
  }

  fn decompress(compressed: &mut BufByteReader, decompressed: &mut Vec<u8>) {
    write!(decompressed, "{}", Self::decompress_as_value(compressed)).unwrap();
  }
}

struct VarBigUint;

impl VarBigUint {
  fn compress(uncompressed: &str, compressed: &mut Vec<u8>) {
    let int = BigUint::parse_bytes(uncompressed.as_bytes(), 10).unwrap();
    let bytes = int.to_bytes_le();
    VarU56::compress_value(bytes.len().try_into().unwrap(), compressed);
    compressed.extend_from_slice(&bytes);
  }

  fn decompress(compressed: &mut BufByteReader, decompressed: &mut Vec<u8>) {
    let byte_len = VarU56::decompress_as_value(compressed);
    let bytes = compressed.read_many(byte_len.try_into().unwrap());
    let int = BigUint::from_bytes_le(bytes);
    write!(decompressed, "{}", int).unwrap();
  }
}

struct BufWithVarLen;

impl BufWithVarLen {
  fn compress(uncompressed: &[u8], compressed: &mut Vec<u8>) {
    VarU56::compress_value(uncompressed.len().try_into().unwrap(), compressed);
    compressed.extend_from_slice(&uncompressed);
  }

  fn decompress(compressed: &mut BufByteReader, decompressed: &mut Vec<u8>) {
    let len = VarU56::decompress_as_value(compressed);
    let bytes = compressed.read_many(len.try_into().unwrap());
    decompressed.extend_from_slice(bytes);
  }
}

#[derive(PartialEq, Eq, Clone, Copy, FromPrimitive)]
#[repr(u8)]
enum PartType {
  // We must be able to derive exact original string, so this only applies to padded Base64 substrings.
  Base64Padded, // BufWithVarLen
  HexLowercase, // BufWithVarLen
  HexUppercase, // BufWithVarLen
  // We must be able to derive exact original string, so we restrict to `Z` and no milliseconds.
  ISOTimestampSecZ, // i64
  // We must be able to derive exact original string, so we restrict to `Z` and exactly four decimal places for seconds.
  ISOTimestampMsZ, // i64
  UuidLowercase,   // [u8; 16]
  UuidUppercase,   // [u8; 16]

  // We must be able to derive exact original string, so none of these must have leading zeros. Creating additional variants that track leading zeros makes it too complex.
  PositiveBase2IntVarU56,      // VarU56
  PositiveBase2IntVarBigUint,  // VarBigUint
  NegativeBase2IntVarU56,      // VarU56
  NegativeBase2IntVarLen,      // VarBigUint
  PositiveBase10IntVarU56,     // VarU56
  PositiveBase10IntVarBigUint, // VarBigUint
  NegativeBase10IntVarU56,     // VarU56
  NegativeBase10IntVarBigUint, // VarBigUint

  Literal, // BufWithVarLen

  // TODO Maybe also have lowercase and uppercase variants, if they're common transformations of base dictionary subseqs? However, this does seem unlikely.
  Top256Subseq,   // u8
  Top65792Subseq, // { idx_minus_256: u16_le }

  // Top 32 u8 bytes.
  Top32Charset, // { original_len: VarU56, compressed: BufWithVarLen }
  // Top 32 ASCII display characters, in either lowercase or uppercase.
  Top32DisplayCharset, // BufWithVarLen
  // Top 32 ASCII display characters, in lowercase.
  Top32DisplayCharsetLowercase, // BufWithVarLen
  // Top 32 ASCII display characters, in uppercase.
  Top32DisplayCharsetUppercase, // BufWithVarLen
}

const fn is_display_char(c: u8) -> bool {
  c >= 32 && c <= 126
}

#[derive(Serialize, Deserialize)]
struct Top32Charset {
  idx_to_byte: [u8; 32],
}

impl Top32Charset {
  // TODO Is this slow? It's on a hot path.
  fn get_index_for_byte(&self, b: u8) -> Option<u8> {
    for i in 0..32 {
      if self.idx_to_byte[i] == b {
        return Some(i as u8);
      };
    }
    None
  }

  pub fn new(bytes: [u8; 32]) -> Self {
    Self { idx_to_byte: bytes }
  }

  /// Returns None if the value cannot be encoded (i.e. contains bytes outside the charset).
  pub fn encode(&self, orig: &[u8]) -> Option<Vec<u8>> {
    let mut out = Vec::new();
    for chunk in orig.chunks(5) {
      let mut v = 0u64;
      for (i, b) in chunk.iter().enumerate() {
        let idx = self.get_index_for_byte(*b)?;
        v |= (idx as u64) << (i * 5);
      }
      out.extend_from_slice(&v.to_le_bytes());
    }
    while out.last().filter(|b| **b == 0).is_some() {
      out.pop().unwrap();
    }
    Some(out)
  }

  pub fn decode(&self, mut raw: &[u8], orig_len: usize) -> Vec<u8> {
    let mut out = Vec::new();
    while out.len() < orig_len {
      let mut buf = [0u8; 8];
      let buflen = min(5, raw.len());
      buf[..buflen].copy_from_slice(&raw[..buflen]);
      let mut v = u64::from_le_bytes(buf);
      while out.len() < orig_len {
        out.push(self.idx_to_byte[(v & 0b11111) as usize]);
        v >>= 5;
      }
      raw = &raw[buflen..];
    }
    out
  }
}

const SUBSEQ_LEN_MIN: usize = 4;
const SUBSEQ_LEN_MAX: usize = 24;

#[derive(Clone, Copy, PartialEq, Eq, FromPrimitive)]
enum RegexPattern {
  // WARNING: These must be in the same order as `re_groups.push` calls in `Dictionary::new`.
  TopSubseq,
  IntPosBase10U56,
  IntPosBase10BigUint,
  IntNegBase10U56,
  IntNegBase10BigUint,
  UuidLowercase,
  UuidUppercase,
  HexLowercase,
  HexUppercase,
  Base64Padded,
}

#[derive(Serialize, Deserialize)]
pub struct DictionaryData {
  top_subseqs: Vec<Vec<u8>>,
  top32_charset: Top32Charset,
}

impl DictionaryData {
  /// Used for debugging. Message format is unspecified and can change at any time.
  pub fn generate_inspection_message(&self) -> String {
    let mut out = String::new();
    out.push_str("Top 32 characters:\n");
    out.push_str("------------------\n");
    out.push_str("\n");
    out.push_str("  ");
    for i in 0..32 {
      write!(out, "    {:>2}", i).unwrap();
    }
    out.push_str("\n");
    out.push_str("  ");
    for _ in 0..32 {
      out.push_str("    --");
    }
    out.push_str("\n");
    out.push_str("  ");
    for b in self.top32_charset.idx_to_byte {
      if is_display_char(b) && b != b' ' {
        write!(out, "     {}", char::from(b)).unwrap();
      } else {
        write!(out, "  \\x{:02x}", b).unwrap();
      };
    }
    out.push_str("\n");
    out.push_str("\n");

    out.push_str("Top subseqs:\n");
    out.push_str("----------------\n");
    out.push_str("\n");
    for subseq in self.top_subseqs.iter() {
      match str::from_utf8(&subseq) {
        Ok(s) => {
          out.push_str("lit ");
          out.push_str(s);
        }
        Err(_) => {
          out.push_str("hex ");
          for c in subseq {
            write!(out, "{:02x}", c).unwrap();
          }
        }
      };
      out.push_str("\n");
    }

    out
  }
}

pub struct Dictionary {
  re: Regex,
  top_subseqs: Vec<Vec<u8>>,
  top32_charset: Top32Charset,
}

impl Dictionary {
  pub fn new(data: DictionaryData) -> Self {
    // Unfortunately, the `regex` crate doesn't support longest-first alternate group matching, so the only way is to individually match against each Regex and find the longest length. Even then, the "best" choice is actually the one with the highest compression ratio, not the longest uncompressed match length, so we'd have to match against all regexes and perform calculations (i.e. figure out compressed length, then compression ratio) anyway. A RegexSet doesn't help, because it doesn't tell us where the match is, only which regexes matched; additional regex matching is still required.
    // Therefore, we use one regex, and don't do any calculations, instead using a basic universal "guess" as to which match type would be best, and then build one regex with one alternate capturing group for each match type ordered by preference. This is important for performance, as compression and decompression will be on small strings and very hot paths, and degrading to multiple linear regex scans, branching, calculations, etc. has a significant performance impact. The most optimal answer is only knowable by enumerating all possible layout/decompression choices, which is impossible, so we're always making some best-effort-only choices anyway.
    // We combine the dynamic subseqs matching into the same regex so we only need to have one regex and one linear matching pass ever; even using another AhoCorasick would require a separate linear pass.
    let mut re_groups = Vec::<&str>::new();
    // Priority 1: always use interned subseqs where possible, since the compression ratio range is huge.
    // `top_subseqs` should already be ordered by popularity, so the regex alternates will be matched preferring popular subseqs first.
    let re_subreqs = data.top_subseqs.iter().map(|subseq| subseq.iter().map(|b| format!("\\x{:02x}", *b)).join("")).join("|");
    re_groups.push(&re_subreqs);
    // TODO Base 2 integers, timestamps.
    // NOTE: The following regexes do not match against the smallest/shortest possible valid value, as those aren't worth compressing.
    // Next, we'll prefer integers, even ones in the middle of some Base64 or hex encoding, because the compression ratio is around 2.3.
    re_groups.push("[1-9][0-9]{3,15}"); // Integer, positive, base 10, 56-bits. We don't need to exactly match 2^56, as any value above 2^49 requires 8 bytes using VarU56 anyway, which is the same as VarBigUint (1 byte for var len + 7 bytes for arbitrary size integer).
    re_groups.push("[1-9][0-9]{16,}"); // Integer, positive, base 10, BigUint.
    re_groups.push("-[1-9][0-9]{3,15}"); // Integer, negative, base 10, 56-bits.
    re_groups.push("-[1-9][0-9]{16,}"); // Integer, negative, base 10, BigUint.
    // UUIDs.
    re_groups.push("[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}"); // UUID lowercase.
    re_groups.push("[A-F0-9]{8}-[A-F0-9]{4}-[A-F0-9]{4}-[A-F0-9]{4}-[A-F0-9]{12}"); // UUID uppercase.
    // Hex.
    re_groups.push("(?:[a-f0-9]{2}){2,}"); // Hex lowercase.
    re_groups.push("(?:[A-F0-9]{2}){2,}"); // Hex uppercase.
    // Base64.
    re_groups.push("(?:[A-Za-z0-9+/]{4}){2,}(?:[A-Za-z0-9+/][AIQYgow4]==|[A-Za-z0-9+/]{2}[AEIMQUYcgkosw048]=|[A-Za-z0-9+/]{4})"); // Base64 padded. WARNING: Character before first `=` padding must be correct, and not just another Base64 character, or else our Base64 decoder will panic.

    Self {
      re: Regex::new(&re_groups.join("|")).unwrap(),
      top_subseqs: data.top_subseqs,
      top32_charset: data.top32_charset,
    }
  }

  pub fn decompress(&self, compressed: &[u8]) -> Vec<u8> {
    let mut decompressed = Vec::new();
    let mut compressed = BufByteReader(compressed);
    while !compressed.at_end() {
      let typ = PartType::from_u8(compressed.read()).unwrap();
      match typ {
        PartType::Base64Padded => {
          let mut raw = Vec::new();
          BufWithVarLen::decompress(&mut compressed, &mut raw);
          decompressed.append(&mut BASE64.encode(&raw).into_bytes());
        }
        PartType::HexLowercase => {
          let mut raw = Vec::new();
          BufWithVarLen::decompress(&mut compressed, &mut raw);
          decompressed.append(&mut HEXLOWER.encode(&raw).into_bytes());
        }
        PartType::HexUppercase => {
          let mut raw = Vec::new();
          BufWithVarLen::decompress(&mut compressed, &mut raw);
          decompressed.append(&mut HEXUPPER.encode(&raw).into_bytes());
        }
        PartType::UuidLowercase => {
          encode_uuid(&HEXLOWER, compressed.read_many(16), &mut decompressed);
        }
        PartType::UuidUppercase => {
          encode_uuid(&HEXUPPER, compressed.read_many(16), &mut decompressed);
        }

        PartType::PositiveBase10IntVarU56 => {
          VarU56::decompress(&mut compressed, &mut decompressed);
        }
        PartType::PositiveBase10IntVarBigUint => {
          VarBigUint::decompress(&mut compressed, &mut decompressed);
        }
        PartType::NegativeBase10IntVarU56 => {
          decompressed.push(b'-');
          VarU56::decompress(&mut compressed, &mut decompressed);
        }
        PartType::NegativeBase10IntVarBigUint => {
          decompressed.push(b'-');
          VarBigUint::decompress(&mut compressed, &mut decompressed);
        }

        PartType::Literal => {
          BufWithVarLen::decompress(&mut compressed, &mut decompressed);
        }

        PartType::Top256Subseq => {
          let idx = compressed.read();
          decompressed.extend_from_slice(&self.top_subseqs[idx as usize]);
        }
        PartType::Top65792Subseq => {
          let idx = u16::from_le_bytes(compressed.read_many(2).try_into().unwrap());
          decompressed.extend_from_slice(&self.top_subseqs[(idx as usize) + 256]);
        }

        PartType::Top32Charset => {
          let original_len = VarU56::decompress_as_value(&mut compressed);
          let mut raw = Vec::new();
          BufWithVarLen::decompress(&mut compressed, &mut raw);
          decompressed.append(
            &mut self
              .top32_charset
              .decode(&raw, original_len.try_into().unwrap()),
          );
        }

        _ => todo!(),
      }
    }
    decompressed
  }

  pub fn compress(&self, uncompressed: &[u8]) -> Vec<u8> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum MatchType {
      Regex(RegexPattern),
      TopSubseq(usize),
    }
    let mut compressed = Vec::new();
    let mut e = uncompressed;
    loop {
      let longest_match = RE_SET
        .matches(e)
        .into_iter()
        .map(|re_idx| {
          RE[re_idx].find(e).map(|m| {
            (
              MatchType::Regex(RegexPattern::from_usize(re_idx).unwrap()),
              m.start(),
              m.end(),
            )
          })
        })
        .chain(once(self.top_subseq_matcher.find(e).map(|m| {
          let idx = m.pattern().as_u32();
          (MatchType::TopSubseq(idx as usize), m.start(), m.end())
        })))
        .filter_map(|v| v)
        .min_by_key(|&(typ, start, end)| {
          let uncompressed = &e[start..end];
          let compressed_len = match typ {
            MatchType::Regex(re) => match re {
              RegexPattern::Base64Padded => 1 + BASE64.decode_len(uncompressed.len()).unwrap(),
              RegexPattern::HexLowercase => 1 + HEXLOWER.decode_len(uncompressed.len()).unwrap(),
              RegexPattern::HexUppercase => 1 + HEXUPPER.decode_len(uncompressed.len()).unwrap(),
              RegexPattern::IntPosBase10U56 => {
                u64::from_str_radix(unsafe { from_utf8_unchecked(uncompressed) }, 10)
                  .unwrap()
                  .ilog(128)
                  .try_into()
                  .unwrap()
              }
              // TODO This is only approximate.
              RegexPattern::IntPosBase10BigUint => 1 + (uncompressed.len() * 3 / 7),
              RegexPattern::IntNegBase10U56 => {
                u64::from_str_radix(unsafe { from_utf8_unchecked(&uncompressed[1..]) }, 10)
                  .unwrap()
                  .ilog(128)
                  .try_into()
                  .unwrap()
              }
              // TODO This is only approximate.
              RegexPattern::IntNegBase10BigUint => 1 + (uncompressed.len() * 3 / 7),
              RegexPattern::UuidLowercase => 16,
              RegexPattern::UuidUppercase => 16,
            },
            MatchType::TopSubseq(idx) => {
              if idx < 256 {
                1
              } else {
                2
              }
            }
          };
          ordered_float::NotNan::new(compressed_len as f64 / uncompressed.len() as f64).unwrap()
        });
      match longest_match {
        Some((_, start, _)) => {
          // We've found a match, but there could be more compressable data before the match, so recurse on that part.
          let before_match = &e[..start];
          compressed.append(&mut self.compress(before_match));
        }
        None => {
          // We couldn't find any match, so we must handle as literal.
          if !e.is_empty() {
            match self.top32_charset.encode(e) {
              Some(e) => {
                compressed.push(PartType::Top32Charset as u8);
                VarU56::compress_value(
                  e.len().try_into().unwrap(),
                  &mut compressed,
                );
                BufWithVarLen::compress(&e, &mut compressed);
              }
              None => {
                compressed.push(PartType::Literal as u8);
                BufWithVarLen::compress(e, &mut compressed);
              }
            };
          };
        }
      };
      let Some((typ, start, end)) = longest_match else {
        break;
      };
      let m = &e[start..end];
      match typ {
        MatchType::Regex(RegexPattern::Base64Padded) => {
          compressed.push(PartType::Base64Padded as u8);
          BufWithVarLen::compress(
            &BASE64
              .decode(m)
              .expect(&format!("failed to decode Base64 string: {}", unsafe {
                from_utf8_unchecked(m)
              })),
            &mut compressed,
          );
        }
        MatchType::Regex(RegexPattern::HexLowercase) => {
          compressed.push(PartType::HexLowercase as u8);
          BufWithVarLen::compress(&HEXLOWER.decode(m).unwrap(), &mut compressed);
        }
        MatchType::Regex(RegexPattern::HexUppercase) => {
          compressed.push(PartType::HexUppercase as u8);
          BufWithVarLen::compress(&HEXUPPER.decode(m).unwrap(), &mut compressed);
        }
        MatchType::Regex(RegexPattern::IntPosBase10U56) => {
          compressed.push(PartType::PositiveBase10IntVarU56 as u8);
          VarU56::compress(unsafe { from_utf8_unchecked(m) }, &mut compressed);
        }
        MatchType::Regex(RegexPattern::IntPosBase10BigUint) => {
          compressed.push(PartType::PositiveBase10IntVarBigUint as u8);
          VarBigUint::compress(unsafe { from_utf8_unchecked(m) }, &mut compressed);
        }
        MatchType::Regex(RegexPattern::IntNegBase10U56) => {
          compressed.push(PartType::NegativeBase10IntVarU56 as u8);
          VarU56::compress(unsafe { from_utf8_unchecked(&m[1..]) }, &mut compressed);
        }
        MatchType::Regex(RegexPattern::IntNegBase10BigUint) => {
          compressed.push(PartType::NegativeBase10IntVarBigUint as u8);
          VarBigUint::compress(unsafe { from_utf8_unchecked(&m[1..]) }, &mut compressed);
        }
        MatchType::Regex(RegexPattern::UuidLowercase) => {
          compressed.push(PartType::UuidLowercase as u8);
          compressed.extend_from_slice(&decode_uuid(&HEXLOWER, m));
        }
        MatchType::Regex(RegexPattern::UuidUppercase) => {
          compressed.push(PartType::UuidUppercase as u8);
          compressed.extend_from_slice(&decode_uuid(&HEXUPPER, m));
        }
        MatchType::TopSubseq(subseq_idx) => {
          if subseq_idx < 256 {
            compressed.push(PartType::Top256Subseq as u8);
            compressed.push(subseq_idx as u8);
          } else {
            compressed.push(PartType::Top65792Subseq as u8);
            compressed.extend_from_slice(&u16::to_le_bytes((subseq_idx - 256).try_into().unwrap()));
          }
        }
      };
      e = &e[end..];
    }
    compressed
  }
}

pub struct DictionaryBuilder {
  byte_freq: [u64; 256],
  subseq_freq: Trie<u64>,
}

static WORD_RE: Lazy<Regex> = Lazy::new(|| {
  // TODO Keep in sync with SUBSEQ_LEN_MIN and SUBSEQ_LEN_MAX.
  Regex::new(r"[a-zA-Z0-9]{4,24}").unwrap()
});

impl DictionaryBuilder {
  pub fn new() -> Self {
    Self {
      byte_freq: [0u64; 256],
      subseq_freq: Trie::new(),
    }
  }

  pub fn add_sample(&mut self, uncompressed: &[u8]) {
    for &c in uncompressed {
      self.byte_freq[c as usize] += 1;
    }
    // We must track all subseqs, not just ones outside of a RegexPattern match, as otherwise the Base64 matcher will essentially match everything and significantly reduce the effectiveness of subseqs deduplication.
    // We would love to do a far more sophisticated subseq compression algorithm. However, initial attempts at trying to implement full arbitrary subseq (i.e. any offset and length) deduplication only ended up with extremely inefficient and complex code, and there were still plenty of unhandled cases that made it ineffective. Fundamentally, it seems like it's an extremely complex and possibly intractible problem to try and find the "global optimum"; even brute forcing is hard to code and absurdly slow. Therefore, we'll start with this basic mechanism, and can analyse, improve, adapt, and add "smarts" as we go. This simple delimiter-splitting mechanism should work pretty well, because:
    // - Most keys are human-friendly, so usually follow a pattern/format of using words or values separated by delimiters, and most characters represent words or values (i.e. delimiters don't really need to be compressed).
    // - We have a lot of slots in our dictionary, which should cover most non-arbitrary "word" usages, and even inefficient closely-related entries.
    // - It's extremely simple and fast.
    for subseq in WORD_RE.find_iter(uncompressed) {
      *self.subseq_freq.get_or_insert_default(subseq.as_bytes().iter().cloned()) += 1;
    };
  }

  pub fn finalise(self) -> DictionaryData {
    let top_subseqs = self
      .subseq_freq
      .iter()
      // It's possible for `subseq` to be shorter than SUBSEQ_LEN_MIN due to unused intermediate internal nodes.
      // TODO Tune filter count threshold.
      .filter(|(subseq, count)| subseq.len() >= SUBSEQ_LEN_MIN && **count > 1)
      .map(|(subseq, count)| {
        let total_savings = subseq.len() * (*count) as usize;
        (subseq, *count, total_savings)
      })
      .sorted_unstable_by_key(|(_, _, total_savings)| Reverse(*total_savings))
      .map(|(subseq, _, _)| subseq)
      .take(65792)
      .collect_vec();

    // WARNING: Map first, or else the indices aren't actually the byte values.
    let top32_bytes: [u8; 32] = self
      .byte_freq
      .iter()
      .enumerate()
      .map(|(byte, count)| (byte as u8, *count))
      .sorted_unstable_by_key(|(_, count)| Reverse(*count))
      .map(|(byte, _)| byte)
      .take(32)
      .collect_vec()
      .try_into()
      .unwrap();
    let top32_charset = Top32Charset::new(top32_bytes);

    DictionaryData {
      top_subseqs,
      top32_charset,
    }
  }
}
