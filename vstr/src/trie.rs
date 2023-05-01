use std::collections::BTreeMap;

struct TrieNode<V> {
  value: Option<V>,
  // Use BTreeMap to iterate in order and deterministically.
  children: BTreeMap<u8, Box<TrieNode<V>>>,
}

impl<V> Default for TrieNode<V> {
  fn default() -> Self {
    Self {
      value: None,
      children: BTreeMap::new(),
    }
  }
}

pub(crate) struct TrieIter<'a, V> {
  path: Vec<u8>,
  // (trie_node, next_child_key).
  stack: Vec<(&'a TrieNode<V>, u8)>,
}

impl<'a, V> Iterator for TrieIter<'a, V> {
  type Item = (Vec<u8>, &'a V);

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      let (n, next_k) = self.stack.last_mut()?;
      let Some((&k, cn)) = n.children.range(*next_k..).next() else {
        self.path.pop();
        self.stack.pop();
        continue;
      };
      *next_k = k + 1;
      self.path.push(k);
      self.stack.push((cn, 0));
      if cn.value.is_some() {
        return Some((self.path.clone(), cn.value.as_ref().unwrap()));
      };
    }
  }
}

pub(crate) struct Trie<V> {
  root: TrieNode<V>,
}

impl<V: Default> Trie<V> {
  pub fn new() -> Self {
    Self {
      root: TrieNode::default(),
    }
  }

  pub fn insert(&mut self, k: &[u8], v: V) {
    assert!(!k.is_empty());
    let mut cur = &mut self.root;
    for c in k {
      cur = cur.children.entry(*c).or_default();
    }
    cur.value = Some(v);
  }

  pub fn get_or_insert_default(&mut self, k: &[u8]) -> &mut V {
    assert!(!k.is_empty());
    let mut cur = &mut self.root;
    for c in k {
      cur = cur.children.entry(*c).or_default();
    }
    cur.value.get_or_insert_with(|| Default::default())
  }

  pub fn iter<'a>(&'a self) -> TrieIter<'a, V> {
    TrieIter {
      path: Vec::new(),
      stack: vec![(&self.root, 0)],
    }
  }
}

#[cfg(test)]
mod tests {
  use crate::trie::Trie;

  #[test]
  fn test_trie() {
    let mut trie = Trie::new();
    trie.insert(b"abc", 43);
    trie.insert(b"abcd", 920);
    trie.insert(b"bcd", 10600);
    trie.insert(b"abac", 6842);
    trie.insert(b"abc", 21);
    let mut it = trie.iter();
    assert_eq!(it.next(), Some((b"abac".to_vec(), &6842)));
    assert_eq!(it.next(), Some((b"abc".to_vec(), &21)));
    assert_eq!(it.next(), Some((b"abcd".to_vec(), &920)));
    assert_eq!(it.next(), Some((b"bcd".to_vec(), &10600)));
    assert_eq!(it.next(), None);
  }
}
