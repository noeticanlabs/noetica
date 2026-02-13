from ck0_reference_model import simulate, verify_chain


if __name__ == "__main__":
    init = {"V": 0.2, "D": 0.0}
    plan = [
        {"E_k": 0.3, "C_k": 0.1, "B_k": 0.2, "rule_id": "demo.rule"},
        {"E_k": 0.2, "C_k": 0.2, "B_k": 0.2, "rule_id": "demo.rule"},
    ]
    receipts, final_state = simulate(init, plan, d_max=5.0)
    ok, msg = verify_chain(receipts, d_max=5.0)
    print("receipts:", len(receipts), "ok:", ok, msg, "final:", final_state)
