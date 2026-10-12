#pragma once

namespace delta {

class DiagEngine;
struct Expr;

// §11.8.1: an operator yields an integral or a real value, which has no
// member and no built-in method. Reports the member access `access`, a method
// call's callee `(x + 1).run` or a member select `(a < b).m`, where its
// left-hand side is a unary, binary, increment or decrement, or `inside`
// operator's expression. A parenthesized `=` is no such operator: §11.3.6
// gives it the value it assigns, of its left-hand side's type. Defined in
// operator_result_members.cpp.
void ReportOperatorResultMember(const Expr& access, DiagEngine& diag);

}  // namespace delta
