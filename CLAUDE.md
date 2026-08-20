
# General Guidelines
- Only make Git commits when the user explicitly asks for one in that specific instance.

# Rocq/Iris Verification Rules

- **Verify Proof State:** After writing 2-3 tactics, always use the `rocq-mcp` tool to check the current goals and ensure no errors are present.
- **Iris Proof Mode:** When working within an Iris proof (identifiable by the `i` prefix in tactics), prioritize separation logic reasoning. If a goal looks like `P -* Q`, use `iIntros`.
- **Universe Management:** If you encounter a "Universe Inconsistency," do not blindly add `Polymorphic`. Instead, check for recursive definitions that might be lifting types too high.
- **Tactic Style:** Prefer structured proof scripts using `[ ]`, `{ }`, and `-` for subgoals to keep the `.v` files readable.