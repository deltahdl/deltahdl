// A.1.4's bind_directive -- its bind_target_instance, its two forms and the
// instantiation it carries -- and the one thing else a `bind` can open, IEEE
// 1800-2012 §11.11's overload_declaration, which Annex C.2.8 has removed. Moved
// out of parser.cpp, which the C.2.8 report took past the limit
// assert-no-oversized-source-files enforces.

#include "parser/parser.h"

namespace delta {

// Reads A.1.4's bind_target_instance, `hierarchical_identifier
// constant_bit_select`, where A.9.3 gives hierarchical_identifier as
// `[ $root . ] { identifier constant_bit_select . } identifier` and
// constant_bit_select as `{ [ constant_expression ] }`: any identifier of the
// path may be followed by selects, and by more than one of them.
BindTargetInstance Parser::ParseBindTargetInstance() {
  BindTargetInstance target;
  if (Check(TokenKind::kSystemIdentifier) && CurrentToken().text == "$root") {
    Consume();
    Expect(TokenKind::kDot, Subclause("23.11"));
    target.from_root = true;
  }
  std::string path;
  do {
    BindTargetSegment segment;
    segment.name = ExpectIdentifier(Subclause("23.11")).text;
    if (!path.empty()) path.push_back('.');
    path.append(segment.name.data(), segment.name.size());
    while (Match(TokenKind::kLBracket)) {
      segment.selects.push_back(ParseExpr());
      Expect(TokenKind::kRBracket, Subclause("23.11"));
    }
    target.segments.push_back(std::move(segment));
  } while (Match(TokenKind::kDot));
  target.path = ArenaCopy(path);
  return target;
}

// Whether `kind` is one of the fifteen operators IEEE 1800-2012 §11.11 let an
// overload_declaration bind a function to: `+ ++ - -- * ** / % == != < <= >
// >= =`. Annex C.2.8 has that construct deprecated by IEEE 1800-2017 and
// absent from this version, so `bind` followed by one of these is nothing this
// standard writes.
static bool IsOverloadableOperator(TokenKind kind) {
  switch (kind) {
    case TokenKind::kPlus:
    case TokenKind::kPlusPlus:
    case TokenKind::kMinus:
    case TokenKind::kMinusMinus:
    case TokenKind::kStar:
    case TokenKind::kPower:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
    case TokenKind::kEqEq:
    case TokenKind::kBangEq:
    case TokenKind::kLt:
    case TokenKind::kLtEq:
    case TokenKind::kGt:
    case TokenKind::kGtEq:
    case TokenKind::kEq:
      return true;
    default:
      return false;
  }
}

// A.1.4's bind_directive, or null for the removed construct of Annex C.2.8:
// `bind` followed by an operator was IEEE 1800-2012 §11.11's
// overload_declaration, `bind overload_operator function data_type
// function_identifier ( overload_proto_formals ) ;`, which is reported at the
// operator as removed and read on to its ';' so that what follows is still
// read; there is no bind directive in it to record.
BindDirective* Parser::ParseBindDirective() {
  auto bind_loc = CurrentLoc();
  Expect(TokenKind::kKwBind, Subclause("23.11"));
  if (IsOverloadableOperator(CurrentToken().kind)) {
    diag_.Error(CurrentLoc(),
                "operator overloading has been removed; `bind` followed by an "
                "operator was IEEE 1800-2012's overload_declaration, which "
                "this standard no longer has",
                Subclause("C.2.8"));
    SkipToSemicolon(lexer_);
    return nullptr;
  }
  auto* decl = arena_.Create<BindDirective>();
  decl->loc = bind_loc;

  // Which of A.1.4's two forms the directive takes is settled by the token
  // after the target, so the target is read as a bind_target_instance either
  // way and held to bind_target_scope once a ':' names the first form.
  auto target_loc = CurrentLoc();
  decl->target = ParseBindTargetInstance();

  if (Match(TokenKind::kColon)) {
    // A.1.4: bind_target_scope ::= module_identifier | interface_identifier,
    // one name, since §23.11 has it name the module or interface whose
    // instances the list then narrows; an instance path, a select or a
    // `$root .` prefix names an instance instead.
    if (decl->target.from_root || decl->target.segments.size() != 1 ||
        !decl->target.segments[0].selects.empty()) {
      diag_.Error(target_loc,
                  "bind target scope is a module or interface identifier",
                  Subclause("A.1.4"));
    }
    do {
      decl->target_instances.push_back(ParseBindTargetInstance());
    } while (Match(TokenKind::kComma));
  }

  auto mod_tok = ExpectIdentifier(Subclause("23.11"));
  decl->instantiation = ParseModuleInst(mod_tok);
  return decl;
}

// A.1.4 puts a bind_directive among the items of a compilation unit. Answers
// whether one stood at the current position, whether or not it was the removed
// construct that leaves nothing to record.
bool Parser::TryParseUnitBindDirective(CompilationUnit* unit) {
  if (!Check(TokenKind::kKwBind)) return false;
  if (auto* bd = ParseBindDirective()) unit->bind_directives.push_back(bd);
  return true;
}

}  // namespace delta
