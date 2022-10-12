#![feature(int_log)]

use itertools::Itertools;

const LENGTH_WEIGHT: u64 = 1;
const SAFETY_WEIGHT: u64 = 3;
const STRAIGHT_EDGE_COST: u64 = 1;
const DIAG_EDGE_COST: u64 = 2;

fn main() {
    let g = 5;
    let grid_size = g * 2 - 1;
    let graph = Graph::rhombus_grid(grid_size);
    let middle_row = grid_size / 4 * 2;
    let start_node = middle_row * grid_size;
    let end_node = middle_row * grid_size + (grid_size - 1);
    let num_agents = 6;
    let start_state = State {
        positions: vec![start_node; num_agents],
    };
    let end_state = State {
        positions: vec![end_node; num_agents],
    };
    if let Some((cost, path)) = shortest_path(&graph, start_state, end_state) {
        println!("Cost: {}", cost);
        for (step, state) in path.into_iter().enumerate() {
            eprint!("Step: {step}: ");
            for pos in State::from_id(state, graph.edges.len(), num_agents).positions {
                eprint!(
                    "Col: {:.1} Row: {:.1}, ",
                    graph.col(pos) as f64 / 2.0,
                    graph.row(pos) as f64 / 2.0
                );
            }
            eprintln!();
        }
    } else {
        println!("Unreachable!");
    }
}

#[derive(Debug, Clone, PartialEq)]
struct State {
    positions: Vec<usize>,
}

impl State {
    fn bits_per_position(n: usize) -> usize {
        ((2 * n - 1).ilog2()) as usize
    }

    fn from_id(mut id: usize, n: usize, count: usize) -> Self {
        let bits_per_position = Self::bits_per_position(n);
        let mut positions = Vec::with_capacity(count);

        for _ in 0..count {
            positions.push(id % (1 << bits_per_position));
            id >>= bits_per_position;
        }

        Self { positions }
    }

    fn to_id(&self, n: usize) -> usize {
        let bits_per_position = Self::bits_per_position(n);
        assert!(bits_per_position * self.positions.len() < 64);
        let mut id = 0;
        for (idx, pos) in self.positions.iter().enumerate() {
            id |= (pos << (idx * bits_per_position));
        }
        id
    }

    fn reachable_states<'a>(
        &'a self,
        graph: &'a Graph,
    ) -> Box<dyn Iterator<Item = (State, u64)> + 'a> {
        let mut iter: Box<dyn Iterator<Item = (State, u64)> + '_> = Box::new(std::iter::once((
            State {
                positions: Vec::new(),
            },
            0,
        )));
        for &pos in &self.positions {
            iter = Box::new(iter.cartesian_product(graph.edges[pos].iter()).map(
                |(mut s, &(next_pos, w))| {
                    s.0.positions.push(next_pos);
                    s.1 += w;
                    s
                },
            ))
        }
        Box::new(iter.map(|mut s| {
            s.0.positions.sort_unstable();
            s
        }))
    }
}

struct Graph {
    edges: Vec<Vec<(usize, u64)>>,
    k: usize,
}

impl Graph {
    fn rhombus_grid(k: usize) -> Self {
        let mut edges = vec![Vec::new(); k * k];

        for row in 0..k {
            for col in 0..k - 1 {
                if col % 2 == 0 {
                    if row % 2 == 0 {
                        edges[row * k + col].push((row * k + col + 1, STRAIGHT_EDGE_COST));
                        if row > 0 {
                            edges[row * k + col].push(((row - 1) * k + col + 1, DIAG_EDGE_COST));
                        }
                        if row + 1 < k {
                            edges[row * k + col].push(((row + 1) * k + col + 1, DIAG_EDGE_COST));
                        }
                    }
                } else {
                    if row % 2 == 0 {
                        edges[row * k + col].push((row * k + col + 1, STRAIGHT_EDGE_COST));
                    } else {
                        edges[row * k + col].push(((row + 1) * k + col + 1, DIAG_EDGE_COST));
                        edges[row * k + col].push(((row - 1) * k + col + 1, DIAG_EDGE_COST));
                    }
                }
            }
        }

        Graph { edges, k }
    }

    fn safety_dist(&self, x: usize, y: usize) -> u64 {
        (self.row(x).abs_diff(self.row(y)) + self.col(x).abs_diff(self.col(y))) as u64
    }

    fn row(&self, node: usize) -> usize {
        node / self.k
    }

    fn col(&self, node: usize) -> usize {
        node % self.k
    }

    fn max_safety_dist(&self) -> u64 {
        let mut max_dist = 0;
        for x in 0..self.edges.len() {
            for y in 0..self.edges.len() {
                max_dist = std::cmp::max(max_dist, self.safety_dist(x, y));
            }
        }
        max_dist
    }
}

use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};

fn shortest_path(graph: &Graph, start: State, goal: State) -> Option<(u64, Vec<usize>)> {
    let n = graph.edges.len();
    let max_dist = graph.max_safety_dist();
    assert_eq!(start.positions.len(), goal.positions.len());
    let mut dists = BTreeMap::<usize, u64>::new();
    let mut parents = BTreeMap::<usize, usize>::new();
    let mut heap = BinaryHeap::new();
    let start_id = start.to_id(n);
    let goal_id = goal.to_id(n);

    dists.insert(start_id, 0);
    heap.push(Reverse((0, start_id)));

    while let Some(Reverse((cur_cost, state_id))) = heap.pop() {
        if state_id == goal_id {
            let mut path = Vec::new();
            path.push(goal_id);
            while *path.last().unwrap() != start_id {
                path.push(parents[path.last().unwrap()]);
            }
            path.reverse();

            return Some((cur_cost, path));
        }
        let state = State::from_id(state_id, n, start.positions.len());

        if cur_cost > dists[&state_id] {
            continue;
        }

        let mut min_dist = max_dist;
        for (idx, &pos_x) in state.positions.iter().enumerate() {
            for &pos_y in state.positions[idx..].iter().skip(1) {
                min_dist = std::cmp::min(min_dist, graph.safety_dist(pos_x, pos_y));
            }
        }
        let pos_cost = max_dist - min_dist;

        for (next_state, cost) in state.reachable_states(graph) {
            let next_cost = cur_cost + pos_cost * SAFETY_WEIGHT + cost * LENGTH_WEIGHT;
            let next_id = next_state.to_id(n);

            if dists
                .get(&next_id)
                .map(|&other_dist| next_cost < other_dist)
                .unwrap_or(true)
            {
                dists.insert(next_id, next_cost);
                parents.insert(next_id, state_id);
                heap.push(Reverse((next_cost, next_id)));
            }
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_and_from_id() {
        let n = 9;
        let state = State {
            positions: vec![2, 2],
        };
        let id = state.to_id(n);
        eprintln!("{id:b}");
        assert_eq!(State::from_id(id, n, 2), state);
    }
}
