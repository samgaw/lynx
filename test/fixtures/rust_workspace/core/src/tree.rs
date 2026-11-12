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

/// Moves a binary payload into a sequence containing exactly one child.
pub fn singleton(payload: Vec<u8>) -> Node {
    append(Vec::new(), Node::Binary(payload))
}

/// Appends an owned child while preserving every previous child in order.
pub fn append(mut children: Vec<Node>, child: Node) -> Node {
    children.push(child);
    Node::Sequence(children)
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

/// Counts and consumes an owned tree, including every compiler field drop.
pub fn count_owned(node: Node, budget: u16) -> Option<u16> {
    count(&node, budget)
}

#[cfg(test)]
mod tests {
    use super::{count, singleton, Node};

    #[test]
    fn construction_preserves_the_owned_payload() {
        let tree = singleton(vec![0, 255, 195, 40]);
        assert_eq!(count(&tree, 2), Some(2));
        assert_eq!(count(&tree, 1), None);
        let Node::Sequence(children) = tree else {
            panic!("expected a sequence");
        };
        let [Node::Binary(payload)] = children.as_slice() else {
            panic!("expected one binary child");
        };
        assert_eq!(payload, &[0, 255, 195, 40]);
    }

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
