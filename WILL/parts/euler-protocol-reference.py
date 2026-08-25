def read_msg():
    line = sys.stdin.readline()
    if not line:
        sys.exit(0)
    return json.loads(line.strip())


def send_msg(msg):
    print(json.dumps(msg), flush=True)


def call_judge(verdict, code):
    global _JUDGE_INFRA_DOWN
    if _JUDGE_INFRA_DOWN:
        return {"status": "error", "judge_code": "JUDGE_INFRASTRUCTURE_ERROR", "infra": True}
    send_msg({"call": "judge", "verdict": verdict, "code": code})
    result = read_msg()
    if _judge_result_is_infra(result):
        _JUDGE_INFRA_DOWN = True
        if isinstance(result, dict):
            result["infra"] = True
    return result


def lean_true(proof_body: str, high_heartbeats: bool = False) -> str:
    """Wrap a tactic proof body in the standard submission template."""
    hb = "set_option maxHeartbeats 12800000 in\n" if high_heartbeats else ""
    indented = "\n".join(
        "  " + line if line.strip() else ""
        for line in proof_body.strip().split("\n")
    )
    return f"import JudgeProblem\n\n{hb}def submission : Goal := by\n  intro G _ h\n{indented}\n"


def lean_false(n: int, table: list) -> str:
    """Wrap a counterexample table in the standard submission template."""
    return (
        _LEAN_PREAMBLE
        + "set_option maxRecDepth 8000 in\n"
        + f"def submission : Goal := by\n"
        + f"  let m : Magma (Fin {n}) := {{\n"
        + f"    op := finOpTable \"{json.dumps(table)}\"\n"
        + f"  }}\n  refine ⟨Fin {n}, m, ?_⟩\n  decideFin!\n"
    )



def normalise(text: str) -> str:
    """Replace ASCII * with the canonical ◇ operator."""
    return text.replace("*", "◇") if isinstance(text, str) else text


def compile_equation(text: str):
    """Return (variables, lhs_fn, rhs_fn) for use with check_equation."""
    vs = variables_of(text)
    lhs_text, rhs_text = text.split("=", 1)
    var_set = set(vs)
    return vs, _parse_expr(lhs_text, var_set), _parse_expr(rhs_text, var_set)


def check_equation(vs, lhs_fn, rhs_fn, n: int, op) -> bool:
    """Return True iff the equation holds for all assignments on Fin n."""
    for vals in iproduct(range(n), repeat=len(vs)):
        env = {"op": op}
        for v, val in zip(vs, vals):
            env[v] = val
        if lhs_fn(env) != rhs_fn(env):
            return False
    return True


def main():
    startup = read_msg()
    problem = startup["problem"]
    budget  = startup.get("budget", {}).get("timeout_seconds", 3600)
    solve(problem, float(budget))



if __name__ == "__main__":
    import os
    if os.environ.get("JUDGE_MARATHON_MANIFEST"):
        marathon()
    else:
        main()
