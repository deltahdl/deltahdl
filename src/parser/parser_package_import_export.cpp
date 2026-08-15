#include "parser/parser.h"

namespace delta {

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
  item->import_item.package_name =
      Expect(TokenKind::kIdentifier, Subclause("26.3")).text;
  Expect(TokenKind::kColonColon, Subclause("26.3"));
  if (Match(TokenKind::kStar)) {
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.item_name =
        Expect(TokenKind::kIdentifier, Subclause("26.3")).text;
  }
  return item;
}

void Parser::ParseImportDecl(std::vector<ModuleItem*>& items) {
  Expect(TokenKind::kKwImport, Subclause("26.3"));

  if (Check(TokenKind::kStringLiteral)) {
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
    items.push_back(ParseDpiExport(loc));
    return;
  }
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kExportDecl;
  item->loc = loc;
  if (Match(TokenKind::kStar)) {
    item->import_item.package_name = "*";
    Expect(TokenKind::kColonColon, Subclause("26.6"));
    Expect(TokenKind::kStar, Subclause("26.6"));
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.package_name =
        Expect(TokenKind::kIdentifier, Subclause("26.6")).text;
    Expect(TokenKind::kColonColon, Subclause("26.6"));
    if (Match(TokenKind::kStar)) {
      item->import_item.is_wildcard = true;
    } else {
      item->import_item.item_name =
          Expect(TokenKind::kIdentifier, Subclause("26.6")).text;
    }
  }
  items.push_back(item);

  while (Match(TokenKind::kComma)) {
    auto* next = arena_.Create<ModuleItem>();
    next->kind = ModuleItemKind::kExportDecl;
    next->loc = loc;
    next->import_item.package_name =
        Expect(TokenKind::kIdentifier, Subclause("26.6")).text;
    Expect(TokenKind::kColonColon, Subclause("26.6"));
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
