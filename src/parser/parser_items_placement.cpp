// The reports on an item read in a body that does not admit it. Annex A gives
// each body its own item production -- A.1.4's module_item, A.1.6's
// interface_item, A.1.7's program_item, A.1.8's checker_or_generate_item -- and
// Parser::ParseModuleItem in src/parser/parser_items.cpp reads every body
// through one dispatch, so what tells the bodies apart is a report made at the
// item, under the production that leaves it out or the clause that says so in
// prose, with the item still read so that the body resumes after it. These
// are the reports, gathered here from parser_items.cpp to keep both files
// inside the limit assert-no-oversized-source-files enforces.

#include <cstddef>
#include <string_view>
#include <vector>

#include "parser/parser.h"

namespace delta {

// A.1.8's checker_or_generate_item lists what a checker body holds: a
// checker_or_generate_item_declaration, which is a `[ rand ]`
// data_declaration, a function_declaration, a checker_declaration, an
// assertion_item_declaration, a covergroup_declaration, a
// genvar_declaration, a clocking_declaration, `default clocking`, `default
// disable iff` or ';'; an initial_construct, an always_construct, a
// final_construct, an assertion_item, a continuous_assign or a
// checker_generate_item. The bodies A.1.4, A.1.6, A.1.7 and A.1.11 give a
// module, an interface, a program and a package reach more through
// module_or_generate_item_declaration and module_common_item -- a
// task_declaration, a class_declaration, a parameter_declaration, a
// parameter_override, a net_alias, a bind_directive, a gate_instantiation and
// a timeunits_declaration among them -- and the parser reads every body
// through the same dispatch. So an item on that wider list is reported here
// under A.1.8, at the token that opens it, when the body being read is a
// checker's; the item is still read, so that the body resumes after it. §17.2
// says the same of the design elements in prose, "modules, interfaces,
// programs, and packages shall not be declared inside checkers", and the
// elaborator reports those with the nets §17.7 refuses.
void Parser::RejectInCheckerBody(const char* msg) {
  if (!InCheckerBody()) return;
  diag_.Error(CurrentLoc(), msg, Subclause("A.1.8"));
}

// A.1.7's non_port_program_item lists what a program body holds beside its
// port declarations: a continuous_assign, a
// module_or_generate_item_declaration, an initial_construct, a final_construct,
// a concurrent_assertion_item, a timeunits_declaration and a
// program_generate_item. A.1.4's module_common_item and module_or_generate_item
// reach more -- a net_alias, a bind_directive, a parameter_override and,
// through assertion_item, a deferred_immediate_assertion_item -- and the parser
// reads every body through the same dispatch, so an item on that wider list is
// reported here under A.1.7 when the body being read is a program's, and still
// read, so that the body resumes after it. §24.3 names the rest of the
// difference in prose, "it shall not contain always procedures, primitives,
// UDPs, or declarations or instances of modules, interfaces, or other
// programs", and those are reported under §24.3 where each is read. An
// anonymous program sets no current_module_ and is left to
// FilterAnonymousProgramItems in parser.cpp, which reports under A.1.11.
void Parser::RejectInProgramBody(SourceLoc loc, const char* msg) {
  if (!InProgramBlock()) return;
  diag_.Error(loc, msg, Subclause("A.1.7"));
}

// A.1.11's package_item is a package_or_generate_item_declaration, an
// anonymous_program, a package_export_declaration or a timeunits_declaration,
// and package_or_generate_item_declaration is a net_declaration, a
// data_declaration, a task_declaration, a function_declaration, a
// checker_declaration, a dpi_import_export, an extern_constraint_declaration,
// a class_declaration, an interface_class_declaration, a
// class_constructor_declaration, a local_parameter_declaration, a
// parameter_declaration, a covergroup_declaration, an
// assertion_item_declaration or ';'. §26.2 has the same in prose: "items
// within packages are generally type definitions, tasks, and functions", with
// "parameters, variables, and nets" beside them. The parser reads a package
// body through the dispatch every body shares, so an item A.1.4's module
// body reaches beyond that list is reported here under A.1.11. Two are
// reported where they are read, because neither reaches the items a package
// records: a bind_directive is kept on the design element being read and a
// package is none, and a generate_region's items are read into the region's
// holder. A port_declaration is reported from TryRejectBodyPortDecl. The rest
// are reported from FilterPackageItems, by the kind each was recorded with.
void Parser::RejectInPackageBody(const char* msg) {
  if (!InPackageBody()) return;
  diag_.Error(CurrentLoc(), msg, Subclause("A.1.11"));
}

// The report FilterPackageItems makes on an item of this kind, or nullptr
// where A.1.11 admits the kind. The three structured procedures are left out:
// the elaborator reports those under §26.2, "variable declaration assignments
// within the package shall occur before any initial or always procedures are
// started", and reads them to do so. A clocking block, a specparam and an
// extern prototype are reported under §14.7, §6.20.5 and A.1.6 where each is
// read. A checker_declaration is the one design element the list admits, and
// a genvar_declaration is recorded as a variable it does not.
static const char* PackageItemRejection(const ModuleItem& item) {
  switch (item.kind) {
    case ModuleItemKind::kContAssign:
      return "a continuous assignment is not an item of a package";
    case ModuleItemKind::kGenerateFor:
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
      return "a generate construct is not an item of a package";
    case ModuleItemKind::kModuleInst:
      return "an instantiation is not an item of a package";
    case ModuleItemKind::kGateInst:
    case ModuleItemKind::kUdpInst:
      return "a primitive instantiation is not an item of a package";
    case ModuleItemKind::kDefparam:
      return "a defparam statement is not an item of a package";
    case ModuleItemKind::kAlias:
      return "a net alias is not an item of a package";
    case ModuleItemKind::kAssertProperty:
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
    case ModuleItemKind::kRestrictProperty:
      return "an assertion statement is not an item of a package; a package "
             "holds property, sequence and let declarations";
    case ModuleItemKind::kElabSystemTask:
      return "an elaboration system task is not an item of a package";
    case ModuleItemKind::kDefaultDisableIff:
      return "a default disable iff declaration is not an item of a package";
    case ModuleItemKind::kNestedModuleDecl:
      return item.nested_module_decl->decl_kind == ModuleDeclKind::kChecker
                 ? nullptr
                 : "a module, interface or program declaration is not an "
                   "item of a package";
    case ModuleItemKind::kVarDecl:
      return item.is_genvar ? "a genvar declaration is not an item of a package"
                            : nullptr;
    default:
      return nullptr;
  }
}

// Reports every item Parser::ParseModuleItem appended to `items` at or after
// `before` that A.1.11 does not admit in a package, and drops it, so that the
// package declares nothing the source could not legally declare in it.
void Parser::FilterPackageItems(std::vector<ModuleItem*>& items,
                                size_t before) {
  size_t kept = before;
  for (size_t i = before; i < items.size(); ++i) {
    ModuleItem* item = items[i];
    const char* rejection = PackageItemRejection(*item);
    if (rejection != nullptr) {
      diag_.Error(item->loc, rejection, Subclause("A.1.11"));
      continue;
    }
    items[kept++] = item;
  }
  items.resize(kept);
}

// A port declaration standing where an item was due. §27.2: a generate block
// may not contain port declarations. Top-level non-ANSI port declarations are
// consumed directly in ParseModuleBody, so a leading port direction reaching
// a generate-block item is always an illegal non-ANSI port declaration. A
// checker body admits none either: A.1.8's checker_or_generate_item has no
// port_declaration, where A.1.4's module_item opens with `port_declaration
// ;`, and a checker's formals are the checker_port_list alone. Either is
// reported and the declaration skipped to its ';', so the body resumes after
// it; returns whether one was found.
bool Parser::TryRejectBodyPortDecl() {
  if (!IsPortDirection(CurrentToken().kind)) return false;
  if (InGenerateBlock()) {
    diag_.Error(CurrentLoc(),
                "port declaration not allowed inside a generate block",
                Subclause("27.2"));
  } else if (InCheckerBody()) {
    diag_.Error(CurrentLoc(),
                "a port declaration is not an item of a checker; its formal "
                "arguments are declared in its port list",
                Subclause("A.1.8"));
  } else if (InPackageBody()) {
    diag_.Error(CurrentLoc(),
                "a port declaration is not an item of a package; a package "
                "has no ports",
                Subclause("A.1.11"));
  } else {
    return false;
  }
  while (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwEnd) &&
         !AtEnd()) {
    Consume();
  }
  Match(TokenKind::kSemicolon);
  return true;
}

// A specify block and a specparam declaration are items of a module body
// alone: A.1.4's non_port_module_item admits specify_block and
// specparam_declaration, and the bodies A.1.6, A.1.7 and A.1.8 give an
// interface, a program and a checker admit neither. §30.3 and §6.20.5 say the
// same in prose, the specify block being "defined within a module" and a
// specparam one that "shall be declared inside a module or specify block". A
// package intercepts its own `specify` in Parser::ParsePackageDecl, and an
// anonymous program is left to FilterAnonymousProgramItems in parser.cpp,
// which reports under A.1.11, so the bodies reported here are the three
// design elements and a package's `specparam`. A generate block is reported
// under §27.2 instead, whichever body holds it, since that is the rule the
// block breaks first.
bool Parser::TryParseSpecifyItem(std::vector<ModuleItem*>& items) {
  if (Check(TokenKind::kKwSpecify)) {
    if (InGenerateBlock()) {
      diag_.Error(CurrentLoc(),
                  "specify block not allowed inside a generate block",
                  Subclause("27.2"));
    } else if (!InModuleBody() && !in_anonymous_program_) {
      diag_.Error(CurrentLoc(),
                  "specify block must appear inside a module declaration",
                  Subclause("30.3"));
    }
    items.push_back(ParseSpecifyBlock());
    return true;
  }
  if (Check(TokenKind::kKwSpecparam)) {
    if (InGenerateBlock()) {
      diag_.Error(CurrentLoc(),
                  "specparam declaration not allowed inside a generate block",
                  Subclause("27.2"));
    } else if (!InModuleBody() && !in_anonymous_program_) {
      diag_.Error(CurrentLoc(),
                  "specparam declaration must appear inside a module or a "
                  "specify block",
                  Subclause("6.20.5"));
    }
    ParseSpecparamDecl(items);
    return true;
  }
  return false;
}

// §24.3 forbids instantiating modules, interfaces and other programs inside a
// program, and the instantiation of a checker is the one a program admits,
// A.1.7's non_port_program_item reaching checker_instantiation through
// concurrent_assertion_item. The two are told apart by the cell's name alone,
// so the report is made for a cell in declared_design_elements_ and every
// other name is left to the elaborator, which reports the rule for a cell
// declared after the program or in another file. Emits the diagnostic so each
// dispatch branch stays flat instead of nesting its own in-program guard.
void Parser::RejectInstInProgram(SourceLoc loc, std::string_view cell,
                                 const char* msg) {
  if (!InProgramBlock() || declared_design_elements_.count(cell) == 0) return;
  diag_.Error(loc, msg, Subclause("24.3"));
}

}  // namespace delta
