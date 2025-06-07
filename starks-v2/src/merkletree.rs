use sha2::{Digest, Sha256};

fn compute_sha256_hex<T>(data: T) -> String
where
    T: AsRef<[u8]>,
{
    let mut hasher = Sha256::new();
    hasher.update(data);
    let result = hasher.finalize();
    format!("{:x}", result)
}

pub fn compute_sha256_bytes<T>(data: T) -> [u8; 32]
where
    T: AsRef<[u8]>,
{
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}

#[derive(Debug, Clone)]
pub struct MerklePathNode {
    pub hash: String,
    pub is_right_sibling: bool,
}

#[derive(Debug)]
pub struct MerkleTree {
    pub leaves: Vec<String>,
    pub tree: Vec<String>,
}

impl MerkleTree {
    pub fn new<T: AsRef<[u8]>>(leaves: Vec<T>) -> Self {
        let leaves: Vec<String> = leaves
            .into_iter()
            .map(|leaf| compute_sha256_hex(&leaf))
            .collect();
        let mut tree = MerkleTree {
            leaves: leaves.clone(),
            tree: vec![],
        };
        tree.build_tree();
        tree
    }

    fn build_tree(&mut self) {
        let mut current_level = self.leaves.clone();
        self.tree = self.leaves.clone();

        while current_level.len() > 1 {
            let mut next_level = vec![];
            for i in (0..current_level.len()).step_by(2) {
                let combined = {
                    if i + 1 < current_level.len() {
                        current_level[i].clone() + &current_level[i + 1]
                    } else {
                        current_level[i].clone() + &current_level[i]
                    }
                };

                next_level.push(compute_sha256_hex(&combined));
            }
            self.tree.extend_from_slice(&next_level);
            current_level = next_level;
        }
    }

    pub fn get_root(&self) -> Option<&String> {
        self.tree.last()
    }

    pub fn get_proof(&self, leaf_index: usize) -> Option<Vec<MerklePathNode>> {
        if leaf_index >= self.leaves.len() {
            return None;
        }

        let mut proof = Vec::new();
        let mut current_node_relative_idx = leaf_index;
        let mut level_start_global_idx = 0;
        let mut nodes_in_current_level = self.leaves.len();

        while nodes_in_current_level > 1 {
            let is_sibling_right = current_node_relative_idx % 2 == 0;

            let sibling_relative_idx = if is_sibling_right {
                current_node_relative_idx + 1
            } else {
                current_node_relative_idx - 1
            };

            let sibling_global_idx = level_start_global_idx + sibling_relative_idx;

            if sibling_relative_idx < nodes_in_current_level {
                proof.push(MerklePathNode {
                    hash: self.tree[sibling_global_idx].clone(),
                    is_right_sibling: is_sibling_right,
                });
            } else {
                let self_node_global_idx = level_start_global_idx + current_node_relative_idx;
                proof.push(MerklePathNode {
                    hash: self.tree[self_node_global_idx].clone(),
                    is_right_sibling: true,
                });
            }

            level_start_global_idx += nodes_in_current_level;
            current_node_relative_idx /= 2;
            nodes_in_current_level = (nodes_in_current_level + 1) / 2;
        }

        Some(proof)
    }

    pub fn verify_proof(
        leaf_data_unhashed: &str,
        proof: &Vec<MerklePathNode>,
        expected_root: &str,
    ) -> bool {
        let mut current_hash = compute_sha256_hex(leaf_data_unhashed);

        for node in proof {
            current_hash = if node.is_right_sibling {
                compute_sha256_hex(&(current_hash.clone() + &node.hash))
            } else {
                compute_sha256_hex(&(node.hash.clone() + &current_hash))
            };
        }
        current_hash == expected_root
    }
}

#[test]
fn test_single_leaf_tree() {
    let leaves_data = vec!["L1".to_string()];
    let tree = MerkleTree::new(leaves_data);

    let h1 = compute_sha256_hex("L1");
    assert_eq!(tree.get_root(), Some(&h1));
    assert_eq!(tree.leaves, vec![h1.clone()]);
    assert_eq!(tree.tree, vec![h1.clone()]);

    let proof = tree.get_proof(0).unwrap();
    assert!(
        proof.is_empty(),
        "Proof for a single leaf tree should be empty"
    );
    assert!(MerkleTree::verify_proof("L1", &proof, &h1));
}

#[test]
fn test_two_leaf_tree() {
    let leaves_data = vec!["L1".to_string(), "L2".to_string()];
    let tree = MerkleTree::new(leaves_data);

    let h1 = compute_sha256_hex("L1");
    let h2 = compute_sha256_hex("L2");
    let root_val = compute_sha256_hex(&(h1.clone() + &h2));

    assert_eq!(tree.get_root(), Some(&root_val));

    let proof0 = tree.get_proof(0).unwrap();
    let expected_proof0 = vec![MerklePathNode {
        hash: h2.clone(),
        is_right_sibling: true,
    }];
    assert_eq!(proof0.len(), expected_proof0.len());
    assert_eq!(proof0[0].hash, expected_proof0[0].hash);
    assert_eq!(
        proof0[0].is_right_sibling,
        expected_proof0[0].is_right_sibling
    );
    assert!(MerkleTree::verify_proof("L1", &proof0, &root_val));

    let proof1 = tree.get_proof(1).unwrap();
    let expected_proof1 = vec![MerklePathNode {
        hash: h1.clone(),
        is_right_sibling: false,
    }];
    assert_eq!(proof1.len(), expected_proof1.len());
    assert_eq!(proof1[0].hash, expected_proof1[0].hash);
    assert_eq!(
        proof1[0].is_right_sibling,
        expected_proof1[0].is_right_sibling
    );
    assert!(MerkleTree::verify_proof("L2", &proof1, &root_val));
}

#[test]
fn test_three_leaf_tree() {
    let leaves_data = vec!["L1".to_string(), "L2".to_string(), "L3".to_string()];
    let tree = MerkleTree::new(leaves_data);

    let h1 = compute_sha256_hex("L1");
    let h2 = compute_sha256_hex("L2");
    let h3 = compute_sha256_hex("L3");

    let h12 = compute_sha256_hex(&(h1.clone() + &h2));
    let h33 = compute_sha256_hex(&(h3.clone() + &h3));
    let root_val = compute_sha256_hex(&(h12.clone() + &h33));

    assert_eq!(tree.get_root(), Some(&root_val));

    let proof0 = tree.get_proof(0).unwrap();
    let expected_proof0 = vec![
        MerklePathNode {
            hash: h2.clone(),
            is_right_sibling: true,
        },
        MerklePathNode {
            hash: h33.clone(),
            is_right_sibling: true,
        },
    ];
    assert_eq!(proof0.len(), expected_proof0.len());
    for i in 0..proof0.len() {
        assert_eq!(proof0[i].hash, expected_proof0[i].hash);
        assert_eq!(
            proof0[i].is_right_sibling,
            expected_proof0[i].is_right_sibling
        );
    }
    assert!(MerkleTree::verify_proof("L1", &proof0, &root_val));

    let proof1 = tree.get_proof(1).unwrap();
    let expected_proof1 = vec![
        MerklePathNode {
            hash: h1.clone(),
            is_right_sibling: false,
        },
        MerklePathNode {
            hash: h33.clone(),
            is_right_sibling: true,
        },
    ];
    assert_eq!(proof1.len(), expected_proof1.len());
    for i in 0..proof1.len() {
        assert_eq!(proof1[i].hash, expected_proof1[i].hash);
        assert_eq!(
            proof1[i].is_right_sibling,
            expected_proof1[i].is_right_sibling
        );
    }
    assert!(MerkleTree::verify_proof("L2", &proof1, &root_val));

    let proof2 = tree.get_proof(2).unwrap();
    let expected_proof2 = vec![
        MerklePathNode {
            hash: h3.clone(),
            is_right_sibling: true,
        },
        MerklePathNode {
            hash: h12.clone(),
            is_right_sibling: false,
        },
    ];
    assert_eq!(proof2.len(), expected_proof2.len());
    for i in 0..proof2.len() {
        assert_eq!(proof2[i].hash, expected_proof2[i].hash);
        assert_eq!(
            proof2[i].is_right_sibling,
            expected_proof2[i].is_right_sibling
        );
    }
    assert!(MerkleTree::verify_proof("L3", &proof2, &root_val));
}

#[test]
fn test_four_leaf_tree() {
    let leaves_data = vec![
        "L1".to_string(),
        "L2".to_string(),
        "L3".to_string(),
        "L4".to_string(),
    ];
    let tree = MerkleTree::new(leaves_data);

    let h1 = compute_sha256_hex("L1");
    let h2 = compute_sha256_hex("L2");
    let h3 = compute_sha256_hex("L3");
    let h4 = compute_sha256_hex("L4");

    let h12 = compute_sha256_hex(&(h1.clone() + &h2));
    let h34 = compute_sha256_hex(&(h3.clone() + &h4));
    let root_val = compute_sha256_hex(&(h12.clone() + &h34));
    assert_eq!(tree.get_root(), Some(&root_val));

    let proof0 = tree.get_proof(0).unwrap();
    let expected_proof0 = vec![
        MerklePathNode {
            hash: h2.clone(),
            is_right_sibling: true,
        },
        MerklePathNode {
            hash: h34.clone(),
            is_right_sibling: true,
        },
    ];
    assert_eq!(proof0.len(), expected_proof0.len());
    for i in 0..proof0.len() {
        assert_eq!(proof0[i].hash, expected_proof0[i].hash);
        assert_eq!(
            proof0[i].is_right_sibling,
            expected_proof0[i].is_right_sibling
        );
    }
    assert!(MerkleTree::verify_proof("L1", &proof0, &root_val));

    let proof2 = tree.get_proof(2).unwrap();
    let expected_proof2 = vec![
        MerklePathNode {
            hash: h4.clone(),
            is_right_sibling: true,
        },
        MerklePathNode {
            hash: h12.clone(),
            is_right_sibling: false,
        },
    ];
    assert_eq!(proof2.len(), expected_proof2.len());
    for i in 0..proof2.len() {
        assert_eq!(proof2[i].hash, expected_proof2[i].hash);
        assert_eq!(
            proof2[i].is_right_sibling,
            expected_proof2[i].is_right_sibling
        );
    }
    assert!(MerkleTree::verify_proof("L3", &proof2, &root_val));
}

#[test]
fn test_verify_proof_false_cases() {
    let leaves_data = vec!["L1".to_string(), "L2".to_string(), "L3".to_string()];
    let tree = MerkleTree::new(leaves_data);
    let root_val = tree.get_root().unwrap();

    let h2 = compute_sha256_hex("L2");
    let h3 = compute_sha256_hex("L3");
    let h33 = compute_sha256_hex(&(h3.clone() + &h3));
    let proof0_for_l1 = vec![
        MerklePathNode {
            hash: h2.clone(),
            is_right_sibling: true,
        },
        MerklePathNode {
            hash: h33.clone(),
            is_right_sibling: true,
        },
    ];

    assert!(!MerkleTree::verify_proof("LX", &proof0_for_l1, &root_val));

    let mut tampered_proof = proof0_for_l1.clone();
    tampered_proof[0].hash = compute_sha256_hex("tampered_hash");
    assert!(!MerkleTree::verify_proof("L1", &tampered_proof, &root_val));

    let mut tampered_order_proof = proof0_for_l1.clone();
    tampered_order_proof[0].is_right_sibling = !tampered_order_proof[0].is_right_sibling;
    assert!(
        !MerkleTree::verify_proof("L1", &tampered_order_proof, &root_val),
        "Verification should fail if sibling order is wrong"
    );

    assert!(!MerkleTree::verify_proof(
        "L1",
        &proof0_for_l1,
        &compute_sha256_hex("wrong_root")
    ));

    assert!(
        !MerkleTree::verify_proof("L1", &vec![], &root_val),
        "Verification with empty proof for multi-leaf tree should fail"
    );

    let h1 = compute_sha256_hex("L1");
    let proof1_for_l2 = vec![
        MerklePathNode {
            hash: h1.clone(),
            is_right_sibling: false,
        },
        MerklePathNode {
            hash: h33.clone(),
            is_right_sibling: true,
        },
    ];
    assert!(
        !MerkleTree::verify_proof("L1", &proof1_for_l2, &root_val),
        "Verification should fail if proof is for a different leaf"
    );
}
