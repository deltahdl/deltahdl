#include "parser/parser_headers.h"

#include <format>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser.h"

namespace delta {

void ReportUnwrittenHeaderParts(const ModuleDecl& decl,
                                const HeaderPartLocs& at, DiagEngine& diag) {
  const bool kChecker = decl.decl_kind == ModuleDeclKind::kChecker;
  if (!kChecker && !decl.has_wildcard_ports) return;
  const std::string_view kWhose =
      kChecker ? "a checker header" : "a ( .* ) header";
  if (at.import_loc.IsValid()) {
    diag.Error(at.import_loc,
               std::format("{} writes no package import declaration", kWhose),
               Subclause("A.1.2"));
  }
  if (at.params_loc.IsValid()) {
    diag.Error(at.params_loc,
               std::format("{} writes no parameter port list", kWhose),
               Subclause("A.1.2"));
  }
  if (kChecker && decl.has_wildcard_ports) {
    diag.Error(at.ports_loc, "a checker header has no ( .* ) form",
               Subclause("A.1.2"));
  } else if (decl.is_extern && decl.has_wildcard_ports) {
    diag.Error(at.ports_loc,
               "an extern declaration's header has no ( .* ) form",
               Subclause("A.1.2"));
  }
}

bool Parser::IsAtClassDecl() {
  if (Check(TokenKind::kKwClass)) return true;
  if (!Check(TokenKind::kKwVirtual) && !Check(TokenKind::kKwInterface)) {
    return false;
  }
  auto saved = lexer_.SavePos();
  const bool kVirtual = Check(TokenKind::kKwVirtual);
  Consume();
  if (kVirtual) Match(TokenKind::kKwInterface);
  bool result = Check(TokenKind::kKwClass);
  lexer_.RestorePos(saved);
  return result;
}

void Parser::ParseExtendsArgList(ClassDecl* decl) {
  Consume();
  if (Match(TokenKind::kKwDefault)) {
    decl->extends_has_default = true;
  } else if (!Check(TokenKind::kRParen)) {
    do {
      decl->extends_args.push_back(ParseExpr());
    } while (Match(TokenKind::kComma));
  }
  Expect(TokenKind::kRParen, Subclause("8.17"));
}

namespace {

bool RecordClassExtendsBase(ClassDecl* decl, InterfaceRef ref,
                            bool is_implements, bool has_type_params) {
  bool is_first_base = !is_implements && decl->base_class.empty();
  if (is_first_base) {
    decl->base_class = ref.name;
    decl->base_class_scope = ref.scope;
  }
  if (has_type_params && is_first_base) {
    decl->base_class_type_params = ref.type_params;
  }
  if (is_implements) {
    decl->implements_types.push_back(std::move(ref));
  } else if (!is_first_base) {
    decl->extends_interfaces.push_back(std::move(ref));
  }
  return is_first_base;
}

}  // namespace

void ParserClassHeaderHelpers::ParseHeadKeywords(Parser& p, ClassDecl* decl) {
  decl->is_virtual = p.Match(TokenKind::kKwVirtual);
  decl->is_interface = p.Match(TokenKind::kKwInterface);
  if (decl->is_virtual && decl->is_interface) {
    p.diag_.Error(decl->range.start,
                  "an interface class is not declared virtual",
                  Subclause("A.1.2"));
  }
  p.Expect(TokenKind::kKwClass, Subclause("8.3"));

  if (p.Match(TokenKind::kColon)) {
    if (decl->is_interface) {
      p.diag_.Error(p.CurrentLoc(),
                    "an interface class takes no final specifier",
                    Subclause("A.1.2"));
    }
    p.Expect(TokenKind::kKwFinal, Subclause("8.13"));
    decl->is_final = true;
  }
  if (p.Check(TokenKind::kKwAutomatic) || p.Check(TokenKind::kKwStatic)) {
    p.diag_.Error(p.CurrentLoc(),
                  std::format("a class declaration takes no lifetime; '{}' "
                              "stands where its name belongs",
                              p.CurrentToken().text),
                  Subclause("8.3"));
    p.Consume();
  }
}

void ParserClassHeaderHelpers::ParseBaseType(Parser& p, ClassDecl* decl,
                                             bool is_implements,
                                             Subclause subclause) {
  std::string_view scope;
  auto name = p.Expect(TokenKind::kIdentifier, subclause).text;
  while (p.Match(TokenKind::kColonColon)) {
    scope = name;
    name = p.Expect(TokenKind::kIdentifier, subclause).text;
  }
  std::vector<DataType> tparams;
  const bool kHasTypeParams = p.Check(TokenKind::kHash);
  if (kHasTypeParams) {
    p.Consume();
    tparams = p.ParseTypeParamList();
  }
  RecordClassExtendsBase(decl, {name, std::move(tparams), scope}, is_implements,
                         kHasTypeParams);
  if (!p.Check(TokenKind::kLParen)) return;
  if (is_implements || decl->is_interface) {
    p.diag_.Error(p.CurrentLoc(),
                  std::format("an interface class type in an {} clause "
                              "takes no arguments",
                              is_implements ? "implements" : "extends"),
                  Subclause("A.1.2"));
  }
  if (is_implements) {
    std::vector<Expr*> discard;
    p.ParseParenList(discard);
  } else {
    p.ParseExtendsArgList(decl);
  }
}

void Parser::ParseClassExtendsClause(ClassDecl* decl, bool is_implements) {
  Subclause subclause(is_implements ? "8.26.2" : "8.13");
  ParserClassHeaderHelpers::ParseBaseType(*this, decl, is_implements,
                                          subclause);
  for (SourceLoc comma = CurrentLoc(); Match(TokenKind::kComma);
       comma = CurrentLoc()) {
    if (!is_implements && !decl->is_interface) {
      diag_.Error(comma,
                  "a class extends one class type; only an interface class "
                  "extends several",
                  Subclause("A.1.2"));
    }
    ParserClassHeaderHelpers::ParseBaseType(*this, decl, is_implements,
                                            subclause);
  }
}

}  // namespace delta
