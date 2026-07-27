#include "parser/parser.h"

namespace delta {

// 18.5: speculatively parse one top-level constraint relation as an Expr* and
// record it for the simulator's randomize() translation. The trial parse
// suppresses diagnostics and rewinds the lexer, so it neither consumes input
// nor changes what the token scan reports; special forms/braces are left to it.
// 18.5.13: a soft constraint is the inner expression_or_dist preceded by
// 'soft'. The inner relation is captured into constraint_soft_exprs so the
// simulator can build it as a discardable soft solver constraint. The dist form
// is tried first -- its dist set is not an expression, so a plain parse would
// stop at 'dist' and capture nothing -- then a plain soft relation. The trial
// parse rewinds, leaving the outer token scan to consume 'soft' and the
// relation as it does for a hard one.
void Parser::CaptureSoftConstraintRelation(ClassMember* member) {
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  Consume();  // 'soft'
  auto after_soft = lexer_.SavePos();
  if (!TryCaptureDist(member, /*is_soft=*/true)) {
    lexer_.RestorePos(after_soft);
    Expr* rel = ParseExpr();
    if (rel != nullptr && Check(TokenKind::kSemicolon) && member) {
      member->constraint_soft_exprs.push_back(rel);
    }
  }
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
}

void Parser::CaptureConstraintRelation(ClassMember* member) {
  TokenKind k = CurrentToken().kind;
  // 18.5.13: a soft constraint is the inner expression_or_dist preceded by
  // 'soft'. Capture the inner relation into constraint_soft_exprs so the
  // simulator can build it as a discardable soft solver constraint. Handled
  // before the bail list below (which drops 'soft') so the preference is not
  // silently lost. The trial parse rewinds, leaving the outer token scan to
  // consume 'soft' and the relation as it does for a hard one.
  if (k == TokenKind::kKwSoft) {
    CaptureSoftConstraintRelation(member);
    return;
  }
  // 18.5.4: a uniqueness constraint "unique { range_list }" heads a
  // constraint_expression with the 'unique' keyword, which is not the start of
  // an expression; capture its range_list members before the plain parse below,
  // which would otherwise stop at 'unique' and record nothing. The trial parse
  // rewinds like the others, leaving the outer token scan to consume the form.
  if (k == TokenKind::kKwUnique) {
    auto saved = lexer_.SavePos();
    diag_.PushSuppress();
    TryCaptureUnique(member);
    diag_.PopSuppress();
    lexer_.RestorePos(saved);
    return;
  }
  // 18.5.13.2: a 'disable soft' directive is not a relation to capture as an
  // expression; the token scan recognizes and consumes the whole directive.
  if (k == TokenKind::kKwForeach || k == TokenKind::kKwSolve ||
      k == TokenKind::kKwDist || k == TokenKind::kKwDisable ||
      k == TokenKind::kLBrace || k == TokenKind::kRBrace ||
      k == TokenKind::kSemicolon) {
    return;
  }
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  // 18.5.6: an if-else constraint ("if ( expression ) constraint_set [ else
  // constraint_set ]") begins with the 'if' keyword, which is not the start of
  // an expression; capture it into equivalent implications before the plain
  // parse below.
  // 18.5.5: an implication whose consequent is an unnamed constraint set,
  // "antecedent -> { c1; c2; ... }", is captured next; its RHS brace is not an
  // expression, so the plain expression parse below would not recognize it.
  bool captured = k == TokenKind::kKwIf ? TryCaptureIfElseConstraint(member)
                                        : TryCaptureBracedImplication(member);
  // 18.5.3: an "expression dist { dist_list }" distribution. Its dist set is
  // not an expression, so the plain parse below would stop at 'dist' and
  // capture nothing; recognize the whole form here after rewinding the
  // implication probe's own speculative attempt.
  if (!captured && k != TokenKind::kKwIf) {
    lexer_.RestorePos(saved);
    captured = TryCaptureDist(member);
  }
  if (!captured) {
    lexer_.RestorePos(saved);
    Expr* rel = ParseExpr();
    if (rel != nullptr && Check(TokenKind::kSemicolon) && member) {
      member->constraint_exprs.push_back(rel);
    }
  }
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
}

// 18.5.13.2: consume a 'disable soft constraint_primary' directive inside a
// constraint block, recording the named random variable. Called from the token
// scan with the current token at 'disable'; it consumes through the primary but
// leaves the terminating ';' for the outer scan (which resets the
// relation-start state on it). Only a bare 'identifier ;' primary is recorded —
// that is a variable the scalar solver draws — so a qualified or array/method
// primary (a.x, arr.size()) is consumed but left unrecorded, making the
// directive a no-op on references the solver does not model, as the uniqueness
// and ordering lowerings do. When the variable is recorded, the simulator
// builds a kDisableSoft solver directive that discards the lower-priority soft
// constraints referencing it.
void Parser::CaptureDisableSoftConstraint(ClassMember* member) {
  Consume();  // 'disable'
  // Only 'disable soft' is a legal constraint_expression; if 'soft' does not
  // follow, capture nothing and let the outer scan resume on the next token.
  if (!Match(TokenKind::kKwSoft)) return;
  if (Check(TokenKind::kIdentifier)) {
    Token id = CurrentToken();
    Consume();
    if (Check(TokenKind::kSemicolon) && member != nullptr) {
      ConstraintSoftVarRef ref;
      ref.name = id.text;
      ref.loc = id.loc;
      member->constraint_disable_soft_refs.push_back(ref);
    }
  }
  // Consume any remaining primary tokens up to the ';' (or the block's '}' if a
  // terminator is missing); the outer scan consumes that terminator itself.
  while (!AtEnd() && !Check(TokenKind::kSemicolon) &&
         !Check(TokenKind::kRBrace)) {
    Consume();
  }
}

// 18.5.5: capture an implication of the form "antecedent -> { c1; c2; ... }".
// Because "A -> { c1; c2 }" is equivalent to (A -> c1) && (A -> c2), each
// consequent relation is captured as its own implication expression "A -> ci",
// an ordinary '->' expression the randomize() translation already enforces via
// its Boolean equivalent (!A || ci). Returns true only when the full braced
// form is recognized; on any mismatch it returns false and captures nothing, so
// the caller falls back to the plain single-relation parse. Runs inside the
// caller's suppressed, position-saved speculative scan.
bool Parser::TryCaptureBracedImplication(ClassMember* member) {
  // The implication operator '->' has the lowest infix binding power, so
  // parsing at a binding power just above it consumes the whole antecedent
  // expression and stops at the '->'.
  Expr* antecedent = ParseExprBp(3);
  if (antecedent == nullptr || !Check(TokenKind::kArrow)) return false;
  Consume();  // '->'
  if (!Check(TokenKind::kLBrace))
    return false;  // only the braced-set form here
  Consume();       // '{'
  std::vector<Expr*> synthesized;
  while (!Check(TokenKind::kRBrace)) {
    if (AtEnd()) return false;
    Expr* consequent = ParseExpr();
    if (consequent == nullptr || !Check(TokenKind::kSemicolon)) return false;
    Consume();  // ';'
    Expr* impl = arena_.Create<Expr>();
    impl->kind = ExprKind::kBinary;
    impl->op = TokenKind::kArrow;
    impl->lhs = antecedent;
    impl->rhs = consequent;
    impl->range.start = antecedent->range.start;
    impl->range.end = consequent->range.end;
    synthesized.push_back(impl);
  }
  Consume();  // '}'
  if (member) {
    for (Expr* impl : synthesized) member->constraint_exprs.push_back(impl);
  }
  return true;
}

// 18.5.3: parse an optional dist_weight ( ':=' expression | ':/' expression )
// onto 'item'. The ':=' operator applies the weight to each element of a range
// (per_element); ':/' applies it to the item as a whole. Returns true when a
// weight operator was consumed, false when none is present (leaving item.weight
// null, which the simulator reads as the default weight of 1). Runs inside the
// caller's suppressed, position-saved speculative scan.
bool Parser::ParseDistWeight(ConstraintDistItem& item) {
  if (MatchColonSlash()) {  // ':/'
    item.per_element = false;
    item.weight = ParseExpr();
    return item.weight != nullptr;
  }
  if (Check(TokenKind::kColon)) {  // possible ':='
    auto saved = lexer_.SavePos();
    Consume();  // ':'
    if (Check(TokenKind::kEq)) {
      Consume();  // '='
      item.per_element = true;
      item.weight = ParseExpr();
      return item.weight != nullptr;
    }
    lexer_.RestorePos(saved);
  }
  return false;
}

// 18.5.3: capture "expression dist { dist_list }". Parses the target
// expression, then each dist_item — a single value, a '[lo:hi]' range, or the
// 'default' item — with its optional dist_weight, recording them on the member
// so the simulator can build a weighted-value distribution constraint. Returns
// false on any structural mismatch (so the plain-relation fallback still runs)
// and records nothing until the whole form is recognized. A range that carries
// no explicit weight defaults to ':= 1' semantics, so per_element is set for
// it. Runs inside the caller's suppressed, position-saved speculative scan.
// 18.5.3 / Syntax 18-3: one dist_item of a distribution's dist_list -- a
// `default` entry (which requires an explicit ':/ expr' weight), a value range
// (a bare range distributing weight 1 per element), or a single value (whose
// weight defaults to 1 when absent).
bool Parser::ParseDistItem(ConstraintDistItem& item) {
  if (Match(TokenKind::kKwDefault)) {
    item.is_default = true;
    return ParseDistWeight(item);
  }
  if (Match(TokenKind::kLBracket)) {
    item.is_range = true;
    item.lo = ParseExpr();
    if (item.lo == nullptr || !Match(TokenKind::kColon)) return false;
    item.hi = ParseExpr();
    if (item.hi == nullptr || !Match(TokenKind::kRBracket)) return false;
    if (!ParseDistWeight(item)) item.per_element = true;
    return true;
  }
  item.value = ParseExpr();
  if (item.value == nullptr) return false;
  ParseDistWeight(item);
  return true;
}

bool Parser::TryCaptureDist(ClassMember* member, bool is_soft) {
  Expr* target = ParseExpr();
  if (target == nullptr || !Check(TokenKind::kKwDist)) return false;
  Consume();  // 'dist'
  if (!Check(TokenKind::kLBrace)) return false;
  Consume();  // '{'
  ConstraintDistRef ref;
  ref.target = target;
  while (!Check(TokenKind::kRBrace)) {
    if (AtEnd()) return false;
    ConstraintDistItem item;
    if (!ParseDistItem(item)) return false;
    ref.items.push_back(item);
    if (!Check(TokenKind::kRBrace) && !Match(TokenKind::kComma)) return false;
  }
  Consume();  // '}'
  // 18.5.13: a dist preceded by 'soft' is a discardable soft distribution; keep
  // it apart from the hard distributions so the simulator lowers it as soft.
  if (member) {
    if (is_soft)
      member->constraint_soft_dist_refs.push_back(ref);
    else
      member->constraint_dist_refs.push_back(ref);
  }
  return true;
}

// 18.5.4 / Syntax 18-4: capture a uniqueness constraint
// "unique { range_list }". The range_list is a comma-separated list of member
// expressions, each denoting a singular variable, an unpacked-array variable,
// or a slice of one. The whole group is recorded on the member so the simulator
// can build a kUnique solver constraint and the elaborator can check the
// restricted member forms. Returns true only when the full form is recognized;
// on any mismatch it captures nothing and returns false so the caller falls
// back to the plain single-relation parse. Runs inside the caller's suppressed,
// position-saved speculative scan.
bool Parser::TryCaptureUnique(ClassMember* member) {
  if (!Check(TokenKind::kKwUnique)) return false;
  Consume();  // 'unique'
  if (!Check(TokenKind::kLBrace)) return false;
  Consume();  // '{'
  std::vector<Expr*> members;
  while (!Check(TokenKind::kRBrace)) {
    if (AtEnd()) return false;
    Expr* item = ParseExpr();
    if (item == nullptr) return false;
    members.push_back(item);
    if (!Check(TokenKind::kRBrace) && !Match(TokenKind::kComma)) return false;
  }
  Consume();  // '}'
  if (member) member->constraint_unique_refs.push_back(std::move(members));
  return true;
}

// 18.5.6: synthesize "guard -> consequent". The if-else form is defined to be
// equivalent to implications, so each guarded relation becomes an ordinary '->'
// expression the randomize() translation already enforces via its Boolean
// equivalent (!guard || consequent). A null guard (no enclosing condition)
// yields the consequent unchanged.
Expr* Parser::MakeConstraintImplication(Expr* guard, Expr* consequent) {
  if (guard == nullptr) return consequent;
  Expr* impl = arena_.Create<Expr>();
  impl->kind = ExprKind::kBinary;
  impl->op = TokenKind::kArrow;
  impl->lhs = guard;
  impl->rhs = consequent;
  impl->range.start = guard->range.start;
  impl->range.end = consequent->range.end;
  return impl;
}

// 18.5.6: build the conjunction "lhs && rhs" used to accumulate an else
// branch's negated conditions with a nested if's own condition.
Expr* Parser::MakeConstraintAnd(Expr* lhs, Expr* rhs) {
  Expr* conj = arena_.Create<Expr>();
  conj->kind = ExprKind::kBinary;
  conj->op = TokenKind::kAmpAmp;
  conj->lhs = lhs;
  conj->rhs = rhs;
  conj->range.start = lhs->range.start;
  conj->range.end = rhs->range.end;
  return conj;
}

// 18.5.6: build the logical negation "!operand", the guard an else branch runs
// under (it applies exactly when the if condition is false).
Expr* Parser::MakeConstraintNot(Expr* operand) {
  Expr* neg = arena_.Create<Expr>();
  neg->kind = ExprKind::kUnary;
  neg->op = TokenKind::kBang;
  neg->lhs = operand;
  neg->range = operand->range;
  return neg;
}

// 18.5.6: capture one constraint_expression inside a guarded branch. It is
// either a nested if-else (handled recursively, so a dangling else binds to its
// closest preceding if) or a single relation, which is recorded as
// "guard -> relation". Returns false on any malformed input so the caller
// captures nothing.
bool Parser::CaptureGuardedConstraintItem(Expr* guard,
                                          std::vector<Expr*>& out) {
  if (Check(TokenKind::kKwIf)) return CaptureGuardedIf(guard, out);
  Expr* rel = ParseExpr();
  if (rel == nullptr || !Check(TokenKind::kSemicolon)) return false;
  Consume();  // ';'
  out.push_back(MakeConstraintImplication(guard, rel));
  return true;
}

// 18.5.6: capture a constraint_set under a guard. The set is either an unnamed
// brace-enclosed group of constraint_expressions or a single constraint
// expression; every relation it contains is guarded by the same condition.
bool Parser::CaptureGuardedConstraintSet(Expr* guard, std::vector<Expr*>& out) {
  if (Check(TokenKind::kLBrace)) {
    Consume();  // '{'
    while (!Check(TokenKind::kRBrace)) {
      if (AtEnd()) return false;
      if (!CaptureGuardedConstraintItem(guard, out)) return false;
    }
    Consume();  // '}'
    return true;
  }
  return CaptureGuardedConstraintItem(guard, out);
}

// 18.5.6: capture "if ( expression ) constraint_set [ else constraint_set ]".
// When the condition holds every then-set relation must be satisfied; otherwise
// every else-set relation must be satisfied. This is encoded as implications:
// the then set runs under the condition and the else set under its negation.
// An outer guard (from an enclosing branch) is conjoined so a nested "else if"
// applies only when every preceding condition failed and its own holds. Assumes
// the current token is 'if'; runs inside the caller's suppressed speculative
// scan and records into 'out' only when the whole form parses.
bool Parser::CaptureGuardedIf(Expr* guard, std::vector<Expr*>& out) {
  Consume();  // 'if'
  if (!Check(TokenKind::kLParen)) return false;
  Consume();  // '('
  Expr* cond = ParseExpr();
  if (cond == nullptr || !Check(TokenKind::kRParen)) return false;
  Consume();  // ')'
  Expr* then_guard = guard ? MakeConstraintAnd(guard, cond) : cond;
  if (!CaptureGuardedConstraintSet(then_guard, out)) return false;
  if (Check(TokenKind::kKwElse)) {
    Consume();  // 'else'
    Expr* neg = MakeConstraintNot(cond);
    Expr* else_guard = guard ? MakeConstraintAnd(guard, neg) : neg;
    if (!CaptureGuardedConstraintSet(else_guard, out)) return false;
  }
  return true;
}

// 18.5.6: entry point for capturing a top-level if-else constraint. Builds the
// synthesized implications into a scratch list and commits them to the member
// only when the whole construct parses, so a malformed if leaves no partial
// relations behind. Returns true when the form was recognized.
bool Parser::TryCaptureIfElseConstraint(ClassMember* member) {
  std::vector<Expr*> out;
  if (!CaptureGuardedIf(/*guard=*/nullptr, out)) return false;
  if (member) {
    for (Expr* impl : out) member->constraint_exprs.push_back(impl);
  }
  return true;
}

// 18.5: scan a constraint block body from just past its opening '{' to the
// matching '}', capturing each top-level relation on 'member' and applying the
// body's structural and reference checks. Shared by an in-class constraint
// block and an external constraint block (18.5.1), so an external block's
// relations are captured the same way and its body receives the same checks.
void Parser::ScanConstraintBodyRelations(ClassMember* member) {
  int depth = 1;
  // 18.5.11: track whether the token just before the current identifier was a
  // '.' or '::' qualifier, so a member/scope-qualified name (obj.f, pkg::f) is
  // not mistaken for an unqualified call on the enclosing class.
  bool prev_was_qualifier = false;
  // 18.5.13.1: true while scanning the expression of a soft constraint, between
  // its 'soft' keyword and the terminating ';'. The bare local variables named
  // in that span are recorded so the elaborator can reject a soft constraint
  // specified on a randc variable.
  bool in_soft = false;
  // 18.5: a new top-level relation begins right after the opening '{' and after
  // each ';'. Capture the relation expression at each such point (see above).
  bool at_relation_start = true;
  while (depth > 0 && !AtEnd()) {
    if (at_relation_start && depth == 1 && !in_soft) {
      CaptureConstraintRelation(member);
    }
    bool starts_with_semicolon = Check(TokenKind::kSemicolon);
    // Carry the previous leaf's '.'/'::' qualifier state for the leaf-token
    // tail (which alone consults it), then reset for this iteration's
    // structural pass.
    bool carried_qualifier = prev_was_qualifier;
    prev_was_qualifier =
        ScanConstraintBodyToken(member, depth, in_soft, carried_qualifier);
    // The next iteration starts a fresh relation only after a ';' was consumed.
    at_relation_start = starts_with_semicolon;
  }
}

ClassMember* Parser::ParseConstraintStub(ClassMember* member) {
  member->kind = ClassMemberKind::kConstraint;
  Consume();

  if (ParseConstraintHeader(member)) return member;

  ScanConstraintBodyRelations(member);
  return member;
}

// 18.5.3: scan a dist_list ('{ dist_item { , dist_item } }') and enforce the
// rules that govern its default specification: it shall use the :/ operator
// (the := operator or an omitted operator is an error), and a distribution
// shall contain at most one default specification.
void Parser::CheckDistSet() {
  if (!Match(TokenKind::kLBrace)) return;
  int depth = 1;
  int default_count = 0;
  while (depth > 0 && !AtEnd()) {
    if (Check(TokenKind::kKwDefault)) {
      Token def = Consume();
      if (++default_count > 1) {
        diag_.Error(def.loc,
                    "a distribution shall contain at most one default "
                    "specification");
      }
      if (CheckColonSlash()) {
        MatchColonSlash();
      } else {
        diag_.Error(def.loc,
                    "a default distribution specification shall use the :/ "
                    "operator");
      }
    } else if (Match(TokenKind::kLBrace)) {
      ++depth;
    } else if (Match(TokenKind::kRBrace)) {
      --depth;
    } else {
      CheckConstraintExprToken(CurrentToken());
      Consume();
    }
  }
}

// Constraint expressions are declarative: 18.3 forbids 4-state values (x or z)
// and 4-state equality operators (=== and !==) inside a constraint, and 18.5
// forbids operators with side effects (++ and --). Both subclauses constrain
// the same constraint_expression construct, so the checks share one scan of
// the constraint block body.
static bool LiteralHasFourStateDigit(std::string_view text) {
  for (char c : text) {
    if (c == 'x' || c == 'X' || c == 'z' || c == 'Z') return true;
  }
  return false;
}

// 18.5.7.1: scan the header of a foreach iterative constraint,
//   foreach ( ps_or_hierarchical_array_identifier [ loop_variables ] )
// where loop_variables is a comma-separated list of optional index variable
// identifiers. The clause makes it an error for a loop variable to reuse the
// identifier of the array being iterated, so take the trailing identifier of
// the (possibly hierarchical) array reference as the array's name and flag any
// loop variable that matches it. Empty loop variables and a trailing run of
// commas are permitted, so an absent identifier between commas is simply
// skipped. The loop-variable count is taken up to the last named slot — a
// trailing run of omittable commas does not inflate it — and recorded, with the
// array name, on the constraint member so the elaborator can check it against
// the array's dimensionality. The constraint_set that follows the header is
// left to the surrounding scan.
namespace {

// 18.5.7.1: the running state of a scan over a foreach header's bracketed
// loop_variables list. bracket_depth is the current '['/']' nesting; slot is
// the 1-based index of the loop-variable slot in view; loop_var_count is the
// index of the last slot that names a variable.
struct ForeachBracketScan {
  int bracket_depth;
  int slot;
  int loop_var_count;
};

// 18.5.7.1: handle one token of a foreach header's bracketed loop_variables
// list, the token having just been consumed by the caller. '[' and ']' adjust
// the bracket nesting depth; at the top level a ',' opens the next
// loop-variable slot, and a loop-variable identifier records the last named
// slot and is an error when it reuses the iterated array's name. Tokens at a
// deeper bracket depth (such as a select expression's contents) only need to be
// skipped, which the caller's consume already accomplished.
void HandleForeachBracketToken(DiagEngine& diag, const Token& t,
                               std::string_view array_name,
                               ForeachBracketScan& scan) {
  if (t.kind == TokenKind::kLBracket) {
    ++scan.bracket_depth;
    return;
  }
  if (t.kind == TokenKind::kRBracket) {
    --scan.bracket_depth;
    return;
  }
  if (scan.bracket_depth == 1 && t.kind == TokenKind::kComma) {
    ++scan.slot;
    return;
  }
  if (scan.bracket_depth == 1 && t.kind == TokenKind::kIdentifier) {
    scan.loop_var_count = scan.slot;
    if (!array_name.empty() && t.text == array_name) {
      diag.Error(t.loc, std::string("foreach loop variable '") +
                            std::string(t.text) +
                            "' may not have the same name as the array it "
                            "iterates over");
    }
  }
}

// 18.5.7.1: record a parsed foreach iterative constraint header on the member
// so the elaborator can check the loop-variable count against the array's
// dimensionality. Headers with no resolvable array name are dropped.
void RecordForeachConstraintRef(ClassMember* member,
                                std::string_view array_name, int loop_var_count,
                                SourceLoc foreach_loc) {
  if (member && !array_name.empty()) {
    ConstraintForeachRef ref;
    ref.array_name = array_name;
    ref.loop_var_count = loop_var_count;
    ref.loc = foreach_loc;
    member->constraint_foreach_refs.push_back(ref);
  }
}

}  // namespace

void Parser::CheckForeachConstraintHeader(ClassMember* member) {
  SourceLoc foreach_loc = CurrentLoc();
  Consume();  // 'foreach'
  if (!Match(TokenKind::kLParen)) return;
  std::string_view array_name;
  // 18.5.7.1: the foreach argument is a ps_or_hierarchical_array_identifier — a
  // plain (possibly package-scoped/hierarchical) name, never a call. A '(' in
  // this position, ahead of the loop_variables bracket, is a function call
  // standing in for the array identifier. It shall be an error to include a
  // function call as an implicit variable declaration in the identifier (see
  // 13.4.1): the header introduces the loop variables as implicit declarations,
  // and a call cannot serve as that declaration.
  while (!Check(TokenKind::kLBracket) && !Check(TokenKind::kRParen) &&
         !AtEnd()) {
    Token t = Consume();
    if (t.kind == TokenKind::kIdentifier) {
      array_name = t.text;
    } else if (t.kind == TokenKind::kLParen) {
      diag_.Error(
          t.loc,
          "a function call may not stand in for the array identifier of "
          "a foreach iterative constraint");
    }
  }
  // bracket_depth: '['/']' nesting; slot: 1-based slot in view; loop_var_count:
  // index of the last slot that names a variable.
  ForeachBracketScan scan{0, 0, 0};
  if (Match(TokenKind::kLBracket)) {
    scan.slot = 1;
    scan.bracket_depth = 1;
    // Every token of the list is consumed exactly once; the per-token bracket
    // depth, slot, and loop-variable bookkeeping is delegated.
    while (scan.bracket_depth > 0 && !AtEnd()) {
      Token t = Consume();
      HandleForeachBracketToken(diag_, t, array_name, scan);
    }
  }
  Match(TokenKind::kRParen);
  RecordForeachConstraintRef(member, array_name, scan.loop_var_count,
                             foreach_loc);
}

// 18.5.9: scan one solve_before_list,
//   solve_before_list ::= constraint_primary { , constraint_primary }
//   constraint_primary ::= [ implicit_class_handle . | class_scope ]
//                          hierarchical_identifier select [ ( ) ]
// recording each constraint_primary's trailing identifier and whether it is a
// bare local variable. A primary that carries a class_scope/implicit-handle
// qualifier (a '.' or '::') or an array-method call ('()', allowed only for an
// array built-in such as size()) is not a simple local variable; the elaborator
// uses that flag to confine the rand/integral restrictions to ordinary
// variables. The list ends at 'before', ';', or the constraint block's '}'.
void Parser::ParseSolveBeforeList(
    std::vector<ConstraintSolveBeforeEntry>& out) {
  while (!AtEnd()) {
    ConstraintSolveBeforeEntry entry;
    bool qualified = false;  // a '.' or '::' qualifier was seen
    bool method = false;     // a trailing '()' was seen
    while (!Check(TokenKind::kComma) && !Check(TokenKind::kKwBefore) &&
           !Check(TokenKind::kSemicolon) && !Check(TokenKind::kRBrace) &&
           !AtEnd()) {
      Token t = Consume();
      if (t.kind == TokenKind::kIdentifier) {
        entry.name = t.text;
      } else if (t.kind == TokenKind::kDot ||
                 t.kind == TokenKind::kColonColon) {
        qualified = true;
      } else if (t.kind == TokenKind::kLParen) {
        method = true;
      }
    }
    entry.is_simple = !qualified && !method;
    if (!entry.name.empty()) out.push_back(entry);
    if (!Match(TokenKind::kComma)) break;
  }
}

void Parser::CheckSolveBeforeConstraint(ClassMember* member) {
  ConstraintSolveBeforeRef ref;
  ref.loc = CurrentLoc();
  Consume();  // 'solve'
  ParseSolveBeforeList(ref.before);
  // The 'before' keyword separates the two lists; without it the statement is
  // malformed, so leave the recovery to the surrounding block scan.
  if (!Match(TokenKind::kKwBefore)) return;
  ParseSolveBeforeList(ref.after);
  Match(TokenKind::kSemicolon);
  if (member) member->constraint_solve_before_refs.push_back(std::move(ref));
}

void Parser::CheckConstraintExprToken(const Token& tok) {
  switch (tok.kind) {
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:
      // 18.3: 4-state operators are illegal in a constraint.
      diag_.Error(tok.loc,
                  "4-state equality operator is not allowed in a constraint");
      break;
    case TokenKind::kPlusPlus:
    case TokenKind::kMinusMinus:
      // 18.5: operators with side effects are not allowed in a constraint.
      diag_.Error(tok.loc,
                  "operator with side effects is not allowed in a constraint");
      break;
    case TokenKind::kIntLiteral:
    case TokenKind::kUnbasedUnsizedLiteral:
      // 18.3: 4-state values (x or z) are illegal in a constraint.
      if (LiteralHasFourStateDigit(tok.text)) {
        diag_.Error(tok.loc, "4-state value is not allowed in a constraint");
      }
      break;
    default:
      break;
  }
}

}  // namespace delta
