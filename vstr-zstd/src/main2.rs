use std::hash::Hash;
use std::hash::Hasher;
use std::io::Read;
use std::io::Write;
use std::mem::forget;
use zstd::dict::DecoderDictionary;
use zstd::dict::EncoderDictionary;
use zstd::Decoder;
use zstd::Encoder;

// A value between 0 and 21 (inclusive).
const ZSTD_COMPRESSION_LEVEL: i32 = 3;

pub struct UrlCompressor {
  edict: EncoderDictionary<'static>,
  ddict: DecoderDictionary<'static>,
}

// This type exists:
// - So we can some some memory over Box<u8> and Vec<u8> by using a smaller `len` and not storing `cap`. (URLs are not allowed to exceed 2048 bytes by our parser.)
// - For clearer type names.
pub struct CompressedUrl {
  data: *mut u8,
  len: u16,
}

unsafe impl Send for CompressedUrl {}
unsafe impl Sync for CompressedUrl {}

impl CompressedUrl {
  pub fn compressed_bytes(&self) -> &[u8] {
    unsafe { std::slice::from_raw_parts(self.data, self.len as usize) }
  }
}

impl Drop for CompressedUrl {
  fn drop(&mut self) {
    unsafe {
      Vec::from_raw_parts(self.data, self.len as usize, self.len as usize);
    };
  }
}

impl PartialEq for CompressedUrl {
  fn eq(&self, other: &Self) -> bool {
    self.compressed_bytes() == other.compressed_bytes()
  }
}

impl Eq for CompressedUrl {}

impl Hash for CompressedUrl {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.compressed_bytes().hash(state)
  }
}

impl UrlCompressor {
  pub fn new(built_dict: &[u8]) -> Self {
    // TODO Use ::new for {En,De}coderDictionary if it's safe to share a copy i.e. no mutations.
    let ddict = DecoderDictionary::copy(&built_dict);
    let edict = EncoderDictionary::copy(&built_dict, ZSTD_COMPRESSION_LEVEL);
    UrlCompressor { edict, ddict }
  }

  pub fn compress(&self, url: impl AsRef<[u8]>) -> CompressedUrl {
    let url = url.as_ref();
    let mut enc = Encoder::with_prepared_dictionary(Vec::new(), &self.edict).unwrap();
    enc
      .set_pledged_src_size(Some(url.len().try_into().unwrap()))
      .unwrap();

    // We are compressing tiny strings, so remove as much metadata and other extra bytes as possible.
    enc.include_checksum(false).unwrap();
    enc.include_contentsize(false).unwrap();
    enc.include_dictid(false).unwrap();
    enc.include_magicbytes(false).unwrap();

    enc.write_all(url).unwrap();
    let mut out = enc.finish().unwrap();

    out.shrink_to_fit();
    assert_eq!(out.len(), out.capacity());
    let len: u16 = out.len().try_into().unwrap();
    let data = out.as_mut_ptr();
    forget(out);
    CompressedUrl { data, len }
  }

  pub fn decompress(&self, url: CompressedUrl) -> String {
    let mut dec = Decoder::with_prepared_dictionary(url.compressed_bytes(), &self.ddict).unwrap();
    dec.include_magicbytes(false).unwrap();
    let mut out = String::new();
    dec.read_to_string(&mut out).unwrap();
    out
  }
}
