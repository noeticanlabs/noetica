from typing import List, Dict, Any, Callable

from nk0_receipts import verify_chain, hash_obj


def replay_and_verify(
    initial_store: Dict[str, Any],
    receipts: List[Any],
    step_fn: Callable[[Dict[str, Any], int], Dict[str, Any]],
):
    ok, msg = verify_chain(receipts)
    if not ok:
        return False, msg

    store = dict(initial_store)
    for r in receipts:
        if hash_obj(store) != r.input_hash:
            return False, f"input_hash mismatch at step {r.step_id}"
        store_next = step_fn(store, r.step_id)
        if hash_obj(store_next) != r.output_hash:
            return False, f"output_hash mismatch at step {r.step_id}"
        store = store_next
    return True, "replay ok"
