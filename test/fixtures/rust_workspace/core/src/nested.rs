//! Bounded nested tag/length/value parsing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Scan {
    /// Total nodes including the scanned root.
    pub nodes: u16,
    /// Number of bytes consumed by this node and its payload.
    pub consumed: usize,
}

/// Scans one node with a tag and a two-byte network-order payload length.
/// Tag zero contains bytes, tag one child nodes, and tag two UTF-8 text.
/// Both the depth and node budgets are actual protocol limits.
pub fn scan(input: &[u8], depth: u8, nodes: u16) -> Option<Scan> {
    if depth == 0 || nodes == 0 || input.len() < 3 {
        return None;
    }
    let payload_len = u16::from_be_bytes([input[1], input[2]]) as usize;
    let total = payload_len + 3;
    let payload = input.get(3..total)?;
    match input[0] {
        0 => Some(Scan {
            nodes: 1,
            consumed: total,
        }),
        1 => {
            let mut rest = payload;
            let mut used = 1;
            while !rest.is_empty() {
                let child = scan(rest, depth - 1, nodes - used)?;
                used += child.nodes;
                rest = rest.get(child.consumed..)?;
            }
            Some(Scan {
                nodes: used,
                consumed: total,
            })
        }
        2 => match core::str::from_utf8(payload) {
            Ok(_) => Some(Scan {
                nodes: 1,
                consumed: total,
            }),
            Err(_) => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{scan, Scan};

    #[test]
    fn scans_multiple_children_with_exact_depth_and_node_budgets() {
        let input = [1, 0, 8, 0, 0, 0, 2, 0, 2, 195, 169];
        assert_eq!(
            scan(&input, 2, 3),
            Some(Scan {
                nodes: 3,
                consumed: 11
            })
        );
        assert_eq!(scan(&input, 1, 3), None);
        assert_eq!(scan(&input, 2, 2), None);
        assert_eq!(scan(&input, 0, 3), None);
        assert_eq!(scan(&input, 2, 0), None);
        assert_eq!(
            scan(&[0, 0, 2, 0, 255], 1, 1),
            Some(Scan {
                nodes: 1,
                consumed: 5
            })
        );
    }

    #[test]
    fn rejects_malformed_lengths_tags_and_text() {
        for input in [
            &[0, 0][..],
            &[0, 0, 2, 1][..],
            &[3, 0, 0][..],
            &[2, 0, 2, 195, 40][..],
            &[1, 0, 3, 0, 0, 1][..],
        ] {
            assert_eq!(scan(input, 3, 10), None);
        }
    }
}
