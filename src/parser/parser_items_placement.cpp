// The reports on an item read in a body that does not admit it. Annex A gives
// each body its own item production -- A.1.4's module_item, A.1.6's
// interface_item, A.1.7's program_item, A.1.8's checker_or_generate_item -- and
// Parser::ParseModuleItem in src/parser/parser_items.cpp reads every body
// through one dispatch, so what tells the bodies apart is a report made at the
// item, under the production that leaves it out or the clause that says so in
// prose, with the item still read so that the body resumes after it. These
// are the reports, gathered here from parser_items.cpp to keep both files
// inside the limit assert-no-oversized-source-files enforces.

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
