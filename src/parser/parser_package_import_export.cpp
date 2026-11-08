#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/parser.h"
#include "parser/scope_prefix_record.h"
#include "parser/scope_type_names.h"

namespace delta {

void Parser::AdoptTypeNames(const ScopeTypeNames& names) {
  known_types_.insert(names.types.begin(), names.types.end());
  known_nettypes_.insert(names.nettypes.begin(), names.nettypes.end());
  known_udps_.insert(names.udps.begin(), names.udps.end());
}

void Parser::ApplyImportedTypeNames(const ImportItem& item) {
  auto it = package_types_.find(item.package_name);
  if (it == package_types_.end()) return;
  if (item.is_wildcard) {
    AdoptTypeNames(it->second);
    return;
  }
  if (it->second.types.count(item.item_name) != 0) {
    known_types_.insert(item.item_name);
  }
  if (it->second.nettypes.count(item.item_name) != 0) {
    known_nettypes_.insert(item.item_name);
  }
}

ModuleItem* Parser::ParseImportItem() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kImportDecl;
  item->loc = CurrentLoc();

  if (CurrentToken().kind == TokenKind::kSystemIdentifier &&
      CurrentToken().text == "$unit") {
    diag_.Error(CurrentLoc(),
                "the compilation-unit scope cannot be used with an "
                "import declaration",
                Subclause("26.3"));
    Consume();
    if (Check(TokenKind::kColonColon)) Consume();
    if (Check(TokenKind::kStar)) {
      Consume();
      item->import_item.is_wildcard = true;
    } else if (Check(TokenKind::kIdentifier)) {
      item->import_item.item_name = Consume().text;
    }
    return item;
  }
  const Token kPackage = Expect(TokenKind::kIdentifier, Subclause("26.3"));
  item->import_item.package_name = kPackage.text;
  Expect(TokenKind::kColonColon, Subclause("26.3"));
  scope_prefixes_.Forget(kPackage.loc);
  if (Match(TokenKind::kStar)) {
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.item_name =
        Expect(TokenKind::kIdentifier, Subclause("26.3")).text;
  }
  ApplyImportedTypeNames(item->import_item);
  return item;
}

void Parser::ParseImportDecl(std::vector<ModuleItem*>& items) {
  const auto kLoc = CurrentLoc();
  Expect(TokenKind::kKwImport, Subclause("26.3"));

  if (Check(TokenKind::kStringLiteral)) {
    if (InCheckerBody()) {
      diag_.Error(kLoc, "a DPI import declaration is not an item of a checker",
                  Subclause("A.1.8"));
    }
    items.push_back(ParseDpiImport());
    return;
  }
  items.push_back(ParseImportItem());
  while (Match(TokenKind::kComma)) {
    items.push_back(ParseImportItem());
  }
  Expect(TokenKind::kSemicolon, Subclause("26.3"));
}

void Parser::ParseExportDecl(std::vector<ModuleItem*>& items) {
  auto loc = CurrentLoc();
  Expect(TokenKind::kKwExport, Subclause("26.6"));

  if (Check(TokenKind::kStringLiteral)) {
    if (InCheckerBody()) {
      diag_.Error(loc, "a DPI export declaration is not an item of a checker",
                  Subclause("A.1.8"));
    }
    items.push_back(ParseDpiExport(loc));
    return;
  }
  if (current_module_ != nullptr) {
    diag_.Error(loc,
                "a package export declaration is allowed only in a package",
                Subclause("26.6"));
  }
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kExportDecl;
  item->loc = loc;
  if (Match(TokenKind::kStar)) {
    item->import_item.package_name = "*";
    Expect(TokenKind::kColonColon, Subclause("26.6"));
    Expect(TokenKind::kStar, Subclause("26.6"));
    item->import_item.is_wildcard = true;
    items.push_back(item);
    Expect(TokenKind::kSemicolon, Subclause("26.6"));
    return;
  }
  const Token kPackage = Expect(TokenKind::kIdentifier, Subclause("26.6"));
  item->import_item.package_name = kPackage.text;
  Expect(TokenKind::kColonColon, Subclause("26.6"));
  scope_prefixes_.Forget(kPackage.loc);
  if (Match(TokenKind::kStar)) {
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.item_name =
        Expect(TokenKind::kIdentifier, Subclause("26.6")).text;
  }
  items.push_back(item);

  while (Match(TokenKind::kComma)) {
    auto* next = arena_.Create<ModuleItem>();
    next->kind = ModuleItemKind::kExportDecl;
    next->loc = loc;
    const Token kNextPackage =
        Expect(TokenKind::kIdentifier, Subclause("26.6"));
    next->import_item.package_name = kNextPackage.text;
    Expect(TokenKind::kColonColon, Subclause("26.6"));
    scope_prefixes_.Forget(kNextPackage.loc);
    if (Match(TokenKind::kStar)) {
      next->import_item.is_wildcard = true;
    } else {
      next->import_item.item_name =
          Expect(TokenKind::kIdentifier, Subclause("26.6")).text;
    }
    items.push_back(next);
  }
  Expect(TokenKind::kSemicolon, Subclause("26.6"));
}

}  // namespace delta
