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
  root: Option<&'a V>,
  path: Vec<u8>,
  // (trie_node, next_child_key).
  stack: Vec<(&'a TrieNode<V>, u8)>,
}

impl<'a, V> Iterator for TrieIter<'a, V> {
  type Item = (Vec<u8>, &'a V);

  fn next(&mut self) -> Option<Self::Item> {
    // TODO Find a better way of doing this.
    if let Some(v) = self.root.take() {
      return Some((Vec::new(), v));
    };
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

  pub fn get(&self, k: impl IntoIterator<Item = u8>) -> Option<&V> {
    let mut cur = &self.root;
    for c in k {
      cur = cur.children.get(&c)?.as_ref();
    }
    cur.value.as_ref()
  }

  pub fn insert(&mut self, k: impl IntoIterator<Item = u8>, v: V) {
    let mut cur = &mut self.root;
    for c in k {
      cur = cur.children.entry(c).or_default();
    }
    cur.value = Some(v);
  }

  pub fn get_or_insert_default(&mut self, k: impl IntoIterator<Item = u8>) -> &mut V {
    let mut cur = &mut self.root;
    for c in k {
      cur = cur.children.entry(c).or_default();
    }
    cur.value.get_or_insert_with(|| Default::default())
  }

  pub fn update_all_values_in_path(
    &mut self,
    k: impl IntoIterator<Item = u8>,
    mut do_not_update_first_n: usize,
    mut updater: impl FnMut(&[u8], &mut V),
  ) {
    let mut cur_k = Vec::new();
    let mut cur = &mut self.root;
    for c in k {
      cur_k.push(c);
      if do_not_update_first_n > 0 {
        do_not_update_first_n -= 1;
        continue;
      };
      cur = cur.children.entry(c).or_default();
      let v = cur.value.get_or_insert_with(|| Default::default());
      updater(&cur_k, v);
    }
  }

  pub fn iter<'a>(&'a self) -> TrieIter<'a, V> {
    TrieIter {
      root: self.root.value.as_ref(),
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
    trie.insert(b"abc".iter().cloned(), 43);
    trie.insert(b"abcd".iter().cloned(), 920);
    trie.insert(b"bcd".iter().cloned(), 10600);
    trie.insert(b"".iter().cloned(), 1);
    trie.insert(b"abac".iter().cloned(), 6842);
    trie.insert(b"abc".iter().cloned(), 21);
    let mut it = trie.iter();
    assert_eq!(it.next(), Some((b"".to_vec(), &1)));
    assert_eq!(it.next(), Some((b"abac".to_vec(), &6842)));
    assert_eq!(it.next(), Some((b"abc".to_vec(), &21)));
    assert_eq!(it.next(), Some((b"abcd".to_vec(), &920)));
    assert_eq!(it.next(), Some((b"bcd".to_vec(), &10600)));
    assert_eq!(it.next(), None);
  }
}
