//! Read-only traversal of protocol trees with owned payloads and child vectors.

/// A recursive protocol value independent of its wire representation.
#[derive(Debug)]
pub enum Node {
    /// An uninterpreted binary payload.
    Binary(Vec<u8>),
    /// A decoded UTF-8 payload.
    Text(String),
    /// An ordered sequence of protocol values.
    Sequence(Vec<Node>),
}

/// Counts every node, rejecting trees larger than the supplied node budget.
pub fn count(node: &Node, budget: u16) -> Option<u16> {
    if budget == 0 {
        return None;
    }
    match node {
        Node::Binary(_) | Node::Text(_) => Some(1),
        Node::Sequence(children) => {
            let mut used = 1;
            for child in children.as_slice() {
                used += count(child, budget - used)?;
            }
            Some(used)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{count, Node};

    #[test]
    fn counts_nested_siblings_and_rejects_insufficient_budgets() {
        let tree = Node::Sequence(vec![
            Node::Binary(vec![0, 255]),
            Node::Sequence(vec![Node::Text("é".into()), Node::Sequence(vec![])]),
        ]);
        assert_eq!(count(&tree, 5), Some(5));
        assert_eq!(count(&tree, u16::MAX), Some(5));
        assert_eq!(count(&tree, 4), None);
        assert_eq!(count(&tree, 0), None);
        assert_eq!(count(&Node::Sequence(vec![]), 1), Some(1));
    }
}
