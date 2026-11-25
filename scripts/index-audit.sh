#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Run scripts/check.sh first to build the implementation and regression imports.
for name in masked_reporting_smoke masked_event_smoke boundary_index_smoke \
  lean_lce_index_smoke indexed_grid_smoke lean_run_index_smoke lean_p2_tail_smoke \
  lean_context_smoke lean_boundary_mixed_smoke masked_finite_action_smoke \
  masked_progression_smoke masked_cut_smoke boundary_trie_smoke masked_run_discovery_smoke \
  boundary_application_smoke masked_periodic_smoke masked_ordered_smoke \
  boundary_subset_smoke masked_periodic_text_smoke masked_owner_enumeration_smoke \
  boundary_heavy_empty boundary_heavy_smoke masked_cluster_smoke masked_periodic_batch_smoke \
  boundary_start_locate_smoke boundary_start_smoke masked_cluster_cursor_smoke masked_threshold_smoke \
  masked_cluster_bank_smoke \
  boundary_separated_smoke \
  masked_cluster_cut_smoke \
  masked_mutable_progression_smoke \
  masked_source_fanout_smoke \
  masked_cluster_leaders_smoke \
  masked_cluster_mutable_smoke \
  masked_mutable_batch_smoke \
  masked_cluster_mutable_batch_smoke \
  masked_empty_smoke \
  masked_empty_batch_smoke \
  masked_cluster_descriptor_smoke \
  boundary_border_smoke \
  masked_suffix_class_smoke \
  masked_cluster_mutable_store_smoke \
  boundary_border_window_smoke \
  boundary_range_smoke \
  masked_traversal_edge_smoke \
  boundary_border_regular_smoke \
  boundary_range_near_smoke \
  boundary_far_index_smoke \
  masked_traversal_driver_smoke \
  masked_run_catalog_smoke \
  boundary_range_border_smoke \
  residual_separated_smoke \
  residual_strip_schedule_smoke \
  masked_traversal_bank_ready_smoke \
  one_use_range_border_smoke \
  residual_dispatch_smoke \
  one_use_far_aggregate_smoke \
  masked_traversal_dirty_smoke \
  masked_traversal_context_smoke \
  one_use_range_cache_smoke \
  short_outer_band_smoke \
  masked_traversal_aggregate_smoke \
  masked_traversal_neighbor_smoke; do
  echo "Running $name"
  lake env lean --run "audits/$name.lean"
done
