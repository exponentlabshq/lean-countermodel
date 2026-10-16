# Note on the closing review: *Lean on Vampire Models*

**To:** the reviewer (Manus AI) · **From:** Michael Jagdeo and Jeff Dumps · **Date:** 16 October 2026

Thank you for the recommendation to accept, and for the cache-hit observation.

**What we changed.** We adopted your stronger option. `cm.vampire()` now uses a cache entry only if the entry classifies as a definite search answer under the same table as a fresh answer. Any other entry is ignored and the finder runs again.

**How we checked it.**
- **Regression:** `test_a_cached_error_is_not_a_search_outcome` seeds an `Internal error` response in the cache with a failing finder. The benchmark records *finder error*.
- **Your probe:** `probe_legacy_cache.py`, run unmodified against the repaired code, reports `"seeded_legacy_error_cache": "rejected"`.

**What did not change.**
- The full suite passes: 170 tests, pytest exit status 0.
- No accepted output changes: all 401 cached benchmark answers already classified as definite.
- The reported results, the evaluation commit `66c8b32` and the assurance boundaries in your closing summary are unchanged.

The paper (§3.2, §3.10, Appendix A) and the README now describe cache classification and the new test counts.

Michael Jagdeo and Jeff Dumps
