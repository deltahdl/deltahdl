#include <string>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/parser.h"
#include "parser/parser_token_skips.h"

namespace delta {

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

  auto target_loc = CurrentLoc();
  decl->target = ParseBindTargetInstance();

  if (Match(TokenKind::kColon)) {
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

void Parser::ParseBindItem(std::vector<ModuleItem*>& items) {
  RejectInCheckerBody("a bind directive is not an item of a checker");
  RejectInProgramBody(CurrentLoc(),
                      "a bind directive is not an item of a program");
  RejectInPackageBody("a bind directive is not an item of a package");
  auto loc = CurrentLoc();
  auto* bd = ParseBindDirective();
  if (bd != nullptr && current_module_) {
    current_module_->bind_directives.push_back(bd);
  }
  if (bd != nullptr && InGenerateBlock()) {
    bd->in_generate_block = true;
    auto* item = arena_.Create<ModuleItem>();
    item->kind = ModuleItemKind::kBindDirective;
    item->loc = loc;
    item->bind_directive = bd;
    items.push_back(item);
  }
}

bool Parser::TryParseUnitBindDirective(CompilationUnit* unit) {
  if (!Check(TokenKind::kKwBind)) return false;
  if (auto* bd = ParseBindDirective()) unit->bind_directives.push_back(bd);
  return true;
}

}  // namespace delta
