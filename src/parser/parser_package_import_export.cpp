#include "parser/parser.h"

namespace delta {

void Parser::AdoptTypeNames(const ScopeTypeNames& names) {
  known_types_.insert(names.types.begin(), names.types.end());
  known_nettypes_.insert(names.nettypes.begin(), names.nettypes.end());
  // Empty for every caller but AdoptCompilationUnitScope, since A.1.2 admits
  // udp_declaration only as a description and so neither ApplyImportedTypeNames
  // nor AdoptBaseClassTypeNames has a primitive name to hand over.
  known_udps_.insert(names.udps.begin(), names.udps.end());
}

// Applies §26.3's rule that an import declaration "allows identifiers declared
// within packages to be visible within the current scope without a package name
// qualifier" to what the parser reads as a type name. A wildcard item hands
// over every type name the package declared; an explicit item hands over the
// one it names, and only when that name is a type, because §26.3's own example
// imports the enumeration type teeth_t without importing the literal FALSE.
//
// The names land in known_types_ and known_nettypes_, so the TypeNameScope of
// the design element holding the import is what takes them away again at its
// closing keyword, and that is what keeps the import from reaching the module
// after it. A package declared later in the file is absent from package_types_
// and hands over nothing, which §26.3 admits: "The compilation of a package
// shall precede the compilation of scopes in which the package is imported."
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
  item->import_item.package_name =
      Expect(TokenKind::kIdentifier, Subclause("26.3")).text;
  Expect(TokenKind::kColonColon, Subclause("26.3"));
  if (Match(TokenKind::kStar)) {
    item->import_item.is_wildcard = true;
  } else {
    item->import_item.item_name =
        Expect(TokenKind::kIdentifier, Subclause("26.3")).text;
  }
  // Not on the `$unit` path above, which returns before reaching here: §26.3
  // gives an import declaration a package_identifier, and that path has already
  // reported the compilation unit standing where one belongs.
  ApplyImportedTypeNames(item->import_item);
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
