// §8.10 "Static methods": the positions a static method body holds an
// expression in, each written with the name of a non-static class property.
//
// §8.10 says "Access to non-static members or to the special this handle within
// the body of a static method is illegal and results in a compiler error." It
// names no position in that body where the access is permitted, so every
// position ForEachChildExpr in src/elaborator/elaborator_validate_internal.h
// admits is a position the rule reaches, and so is every child link
// AnyExprChild admits one level down.
//
// StmtRefsNonStaticMember read four of those sixteen statement positions and
// ExprRefsNonStaticMember ten of those thirteen links, so an access written
// anywhere else compiled. The cases here are one per position that walk did not
// read.
//
// The cases for the positions it did read -- Stmt::lhs, Stmt::rhs, Stmt::expr
// and Stmt::condition -- and the cases for the statement links ForEachChildStmt
// admits are in test_elaborator_subclause_08_10a.cpp, which the 1000-line cap
// in .github/workflows/deltahdl.yml separated this file from.
//
// The other half of §8.10's sentence, the special `this` handle, is found by
// StmtRefsThisOrSuper standing beside StmtRefsNonStaticMember in that same
// source file, and it wrote out six of the thirteen statement links until
// #3319. The cases at the end of this file are one per link that walk did not
// read, and they stand here rather than in test_elaborator_subclause_08_10a.cpp
// because that file is already the larger half of the split.
//
// The cases at the very end are the accesses §8.10 does not bar: a member read
// or a method called through a handle the static method holds, which
// ExprRefsNonStaticMember reported as the bare access until the left side of a
// `.` access became the only side it searches.

#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The source each case below elaborates, with `stmt` written into the
// begin/end of a static task of a class whose one non-static property is `i`.
//
// A static task rather than a static function, because §13.4 bars a timing
// control from a function body and four of the positions here are timing
// controls; the elaborator enforces that separately in
// Elaborator::ValidateFunctionBody, and a function form would be rejected for
// §13.4 before §8.10 was reached. §8.10 reaches a task and a function alike:
// Elaborator::ValidateOneClassStaticMethods selects on
// ClassMemberKind::kMethod and ModuleItem::is_static and not on which of the
// two it is.
//
// `k`, `a` and `arr` are declared local to the method so a case can assign
// through them without naming a second class member, which would leave the
// report ambiguous about which access it found.
//
// `declares_i` writes `int i;` into the same block. §6.21 says of a declaration
// in a block that "These variables are visible to the unnamed block and any
// nested blocks below it", so the name in the statement under test is then the
// local and not the property. That is the accepting half of each pair below,
// and the pair is what tells the two walks apart: the reporter alone would
// report an access to a name the block does declare, and the collection of the
// names a block declares would suppress a report nothing was making.
std::string StaticMethodBodySrc(const std::string& stmt, bool declares_i) {
  return "class C;\n"
         "  int i;\n"
         "  static task t();\n"
         "    begin\n"
         "      int k;\n"
         "      logic [7:0] a;\n"
         "      int arr[4];\n" +
         std::string(declares_i ? "      int i;\n" : "") + "      " + stmt +
         "\n"
         "    end\n"
         "  endtask\n"
         "endclass\n"
         "module m;\n"
         "  C c;\n"
         "endmodule\n";
}

// The report stands at the method's own declaration rather than at the
// statement holding the access, because §8.10's rule is about the method:
// Elaborator::ValidateOneClassStaticMethods scans a static method body and
// reports the method once.
void ExpectPropertyAccessReported(const std::string& stmt) {
  ElabFixture f;
  std::string src = StaticMethodBodySrc(stmt, false);
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            LineHolding(src, "static task"), "8.10"));
}

void ExpectBlockLocalAccepted(const std::string& stmt) {
  EXPECT_TRUE(ElabOk(StaticMethodBodySrc(stmt, true)));
}

// A.6.8 gives `for ( [for_initialization] ; [expression] ; [for_step] )`, and
// Parser::ParseForStmt puts that middle expression in Stmt::for_cond
// (src/parser/parser_stmt.cpp:563) rather than in Stmt::condition. That is what
// makes this the position that reads as an oversight: the walk read
// Stmt::condition and a `for` keeps its condition somewhere else.
//
// The control variable is `j` and not `i`, because §12.7.1 makes a name
// declared in a for header local to the loop and CollectForHeaderNames in
// src/elaborator/elaborator_validate_static_methods.cpp collects it, which
// would shadow the property and answer a different question.
TEST(StaticMethodExprPositions, PropertyInAForConditionIsReported) {
  ExpectPropertyAccessReported("for (int j = 0; j < i; j = j + 1) k = j;");
}

TEST(StaticMethodExprPositions, BlockLocalInAForConditionIsAccepted) {
  ExpectBlockLocalAccepted("for (int j = 0; j < i; j = j + 1) k = j;");
}

// A.2.4 gives `variable_decl_assignment ::= variable_identifier
// { variable_dimension } [ = expression ]`, and Parser::ParseBlockDataDecl puts
// that expression in Stmt::var_init (src/parser/parser_block_item_decl.cpp).
// This is the position #3321 opens with, because naming a property in the
// initializer of a local is the plainest way there is to write the access.
TEST(StaticMethodExprPositions, PropertyInAVariableInitializerIsReported) {
  ExpectPropertyAccessReported("int j = i;");
}

TEST(StaticMethodExprPositions, BlockLocalInAVariableInitializerIsAccepted) {
  ExpectBlockLocalAccepted("int j = i;");
}

// A.6.5 gives `procedural_timing_control ::= delay_control | event_control |
// cycle_delay`, and Parser::ParseDelayStmt puts a delay_control's expression in
// Stmt::delay (src/parser/parser_stmt.cpp:756).
TEST(StaticMethodExprPositions, PropertyInADelayControlIsReported) {
  ExpectPropertyAccessReported("#(i) k = 1;");
}

TEST(StaticMethodExprPositions, BlockLocalInADelayControlIsAccepted) {
  ExpectBlockLocalAccepted("#(i) k = 1;");
}

// Parser::ParseCycleDelayStmt puts a cycle_delay's expression in
// Stmt::cycle_delay (src/parser/parser_stmt.cpp:739). §14.11 makes `##` need a
// default clocking block, which CollectProceduralRoots in
// src/elaborator/elaborator_validate_clocking.cpp does not reach through a
// class declaration, so the source carries only the §8.10 report.
TEST(StaticMethodExprPositions, PropertyInACycleDelayIsReported) {
  ExpectPropertyAccessReported("##(i) k = 1;");
}

TEST(StaticMethodExprPositions, BlockLocalInACycleDelayIsAccepted) {
  ExpectBlockLocalAccepted("##(i) k = 1;");
}

// A.6.10 gives `simple_immediate_assert_statement ::= assert ( expression )
// action_block`, and ParserAssertHelpers::ParseAssertedExpr puts that
// expression in Stmt::assert_expr (src/parser/parser_assert.cpp:35). The
// statements of the action block are a separate position, covered in
// test_elaborator_subclause_08_10a.cpp.
TEST(StaticMethodExprPositions, PropertyInAnImmediateAssertionIsReported) {
  ExpectPropertyAccessReported("assert (i);");
}

TEST(StaticMethodExprPositions, BlockLocalInAnImmediateAssertionIsAccepted) {
  ExpectBlockLocalAccepted("assert (i);");
}

// A.6.5 gives `delay_or_event_control ::= ... | repeat ( expression )
// event_control`, and Parser::ParseIntraAssignTiming puts that expression in
// Stmt::repeat_event_count (src/parser/parser_stmt.cpp:681). §9.4.2 admits an
// ordinary variable as an event_expression, so `@(a)` needs no event object.
TEST(StaticMethodExprPositions, PropertyInARepeatEventCountIsReported) {
  ExpectPropertyAccessReported("k = repeat (i) @(a) 1;");
}

TEST(StaticMethodExprPositions, BlockLocalInARepeatEventCountIsAccepted) {
  ExpectBlockLocalAccepted("k = repeat (i) @(a) 1;");
}

// A.6.5 gives `event_expression ::= [ edge_identifier ] expression [ iff
// expression ]`, and Parser::ParseSingleEvent puts the first of those in
// EventExpr::signal (src/parser/parser_declaration.cpp:855). Stmt::events holds
// one EventExpr per entry of the list, so the two expressions of an entry are
// two positions and take a case each.
TEST(StaticMethodExprPositions, PropertyInAnEventExpressionIsReported) {
  ExpectPropertyAccessReported("@(i) k = 1;");
}

TEST(StaticMethodExprPositions, BlockLocalInAnEventExpressionIsAccepted) {
  ExpectBlockLocalAccepted("@(i) k = 1;");
}

// The `iff` half of that same production, which Parser::ParseSingleEvent puts
// in EventExpr::iff_condition (src/parser/parser_declaration.cpp:858).
TEST(StaticMethodExprPositions, PropertyInAnEventIffConditionIsReported) {
  ExpectPropertyAccessReported("@(a iff i) k = 1;");
}

TEST(StaticMethodExprPositions, BlockLocalInAnEventIffConditionIsAccepted) {
  ExpectBlockLocalAccepted("@(a iff i) k = 1;");
}

// A.6.5 gives `wait_order ( hierarchical_identifier { , hierarchical_identifier
// } ) action_block`, which Parser::ParseWaitOrderStmt pushes into
// Stmt::wait_order_events (src/parser/parser_clocking.cpp:292). The operands
// are named events rather than arbitrary expressions, so the source declares
// two, and both are non-static properties standing in the same position.
//
// This position has no accepting counterpart. An `event` could not be declared
// inside the method body to shadow the property when this case was written:
// IsDataTypeKeyword, then in src/parser/parser_stmt.cpp and now in
// src/parser/parser_token_skips.h, omitted TokenKind::kKwEvent, so
// Parser::IsBlockVarDeclStartCore refused the line and it was read as an
// expression statement. A.2.1.3 and A.2.2.1 admit `event` in a
// data_declaration, so that was a defect in the parser rather than a rule;
// #3322 recorded it and is closed, and the case stands as it was written.
TEST(StaticMethodExprPositions, PropertyInAWaitOrderListIsReported) {
  ElabFixture f;
  std::string src =
      "class C;\n"
      "  event i;\n"
      "  event j;\n"
      "  static task t();\n"
      "    wait_order (i, j);\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n";
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            LineHolding(src, "static task"), "8.10"));
}

// A.6.7 gives `randcase_item ::= expression : statement_or_null`, and
// Parser::ParseRandcaseStmt puts the weight in the first of each
// Stmt::randcase_items pair (src/parser/parser_verify.cpp:40). The statement in
// the second is a separate position, covered in
// test_elaborator_subclause_08_10a.cpp.
TEST(StaticMethodExprPositions, PropertyInARandcaseWeightIsReported) {
  ExpectPropertyAccessReported("randcase i : k = 1; endcase");
}

TEST(StaticMethodExprPositions, BlockLocalInARandcaseWeightIsAccepted) {
  ExpectBlockLocalAccepted("randcase i : k = 1; endcase");
}

// A.6.7 gives `case_item ::= case_item_expression { , case_item_expression } :
// statement_or_null`, and Parser::ParseCaseItem pushes each of those into
// CaseItem::patterns (src/parser/parser_stmt.cpp:530). The item body is a
// separate position, reached through ForEachChildStmt.
TEST(StaticMethodExprPositions, PropertyInACaseItemPatternIsReported) {
  ExpectPropertyAccessReported("case (k) i: k = 1; endcase");
}

TEST(StaticMethodExprPositions, BlockLocalInACaseItemPatternIsAccepted) {
  ExpectBlockLocalAccepted("case (k) i: k = 1; endcase");
}

// A.2.5 gives `unpacked_dimension ::= [ constant_range ] | [
// constant_expression
// ]`, which Parser::ParseUnpackedDims pushes into Stmt::var_unpacked_dims
// (src/parser/parser_types.cpp:584).
//
// No conforming source reaches this position: §7.4.2 requires a constant
// expression there and a non-static class property is not one. The source
// parses and elaborates with the §8.10 report alone, because the constancy
// walks in src/elaborator/elaborator_validate_queries_dims.cpp key off
// module-level signal names, which a method-local array is not among. The case
// therefore exercises the position while the SystemVerilog is illegal for a
// reason §8.10 has nothing to do with.
TEST(StaticMethodExprPositions, PropertyInAnUnpackedDimensionIsReported) {
  ExpectPropertyAccessReported("int arr2[i];");
}

TEST(StaticMethodExprPositions, BlockLocalInAnUnpackedDimensionIsAccepted) {
  ExpectBlockLocalAccepted("int arr2[i];");
}

// A.6.12 gives `rs_rule ::= rs_production_list [ := weight_specification [
// rs_code_block ] ]`, and Parser::ParseRsRuleWeight puts the weight in
// RsRule::weight (src/parser/parser_verify.cpp:241), which
// ForEachRandsequenceExpr reaches. The code blocks a randsequence holds are
// statements rather than expressions and are covered in
// test_elaborator_subclause_08_10a.cpp.
TEST(StaticMethodExprPositions, PropertyInARandsequenceWeightIsReported) {
  ExpectPropertyAccessReported(
      "randsequence(main) main : alt := i; alt : { ; }; endsequence");
}

TEST(StaticMethodExprPositions, BlockLocalInARandsequenceWeightIsAccepted) {
  ExpectBlockLocalAccepted(
      "randsequence(main) main : alt := i; alt : { ; }; endsequence");
}

// The three Expr child links below are unreachable however many statement
// positions are added, because each is nested inside an expression the walk
// already reached.
//
// A.8.4 gives `part_select_range ::= constant_range | indexed_range`, and
// Parser::ParseSelectExpr puts the first bound in Expr::index and the second in
// Expr::index_end (src/parser/expr_parser.cpp:870). The property therefore has
// to be the second bound: `a[i:3]` would land it in Expr::index, which the walk
// already read, and the case would pass whether the fix existed or not.
//
// §11.5.1 requires both bounds constant, so this source is not conforming
// either; the §11.5.1 bounds check in
// src/elaborator/elaborator_validate_queries_dims.cpp returns early for a name
// it has no declared shape for, so the §8.10 report is the only one.
TEST(StaticMethodExprPositions, PropertyInAPartSelectUpperBoundIsReported) {
  ExpectPropertyAccessReported("k = a[3:i];");
}

TEST(StaticMethodExprPositions, BlockLocalInAPartSelectUpperBoundIsAccepted) {
  ExpectBlockLocalAccepted("k = a[3:i];");
}

// A.8.1 gives `multiple_concatenation ::= { expression concatenation }`, and
// Parser::ParseConcatenation puts that leading expression in Expr::repeat_count
// (src/parser/expr_parser_calls.cpp:126). §11.4.12.1 requires it constant, so
// the same caveat holds as for the part select above.
TEST(StaticMethodExprPositions, PropertyInAReplicationCountIsReported) {
  ExpectPropertyAccessReported("k = {i{1'b0}};");
}

TEST(StaticMethodExprPositions, BlockLocalInAReplicationCountIsAccepted) {
  ExpectBlockLocalAccepted("k = {i{1'b0}};");
}

// A.6.7 gives `array_pattern_key ::= constant_expression | ...`, and
// Parser::ParsePatternElement pushes it into Expr::pattern_keys
// (src/parser/expr_parser_patterns.cpp:199). §10.9.1 requires the key constant,
// so the same caveat holds again.
TEST(StaticMethodExprPositions, PropertyInAnAssignmentPatternKeyIsReported) {
  ExpectPropertyAccessReported("arr = '{i: 1};");
}

TEST(StaticMethodExprPositions, BlockLocalInAnAssignmentPatternKeyIsAccepted) {
  ExpectBlockLocalAccepted("arr = '{i: 1};");
}

// The nine cases below are the other half of §8.10's sentence: the special
// `this` handle, written in each statement link StmtRefsThisOrSuper in
// src/elaborator/elaborator_validate_static_methods.cpp did not read before
// #3319. That walk wrote out six of the thirteen links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h names, so `this` written in a
// fork arm, a for header, either arm of an immediate assertion, a randcase item
// or a randsequence code block named the handle where nothing looked.
//
// The class property below is static, which leaves the source with the one
// report: §8.10's other half needs a non-static member to have anything to say,
// and CollectNonStaticMemberNames finds none here. §8.10 bars `this` in a
// static method whatever the member it qualifies, because
// CheckStaticMethodsForThisSuper searches the body for the handle itself.
//
// A static task rather than a static function, which is the method the
// statement-link cases for the other half of the sentence are written in, in
// test_elaborator_subclause_08_10a.cpp. §8.10 reaches a task and a function
// alike: Elaborator::ValidateOneClassStaticMethods selects on
// ClassMemberKind::kMethod and ModuleItem::is_static and not on which of the
// two it is.
std::string StaticMethodThisSrc(const std::string& stmt) {
  return "class C;\n"
         "  static int x;\n"
         "  static task t();\n"
         "    int k;\n"
         "    " +
         stmt +
         "\n"
         "  endtask\n"
         "endclass\n"
         "module m;\n"
         "  C c;\n"
         "endmodule\n";
}

// The report stands at the method's own declaration rather than at the
// statement holding the handle, because §8.10's rule is about the method:
// CheckStaticMethodsForThisSuper scans a static method body and reports the
// method once.
void ExpectThisReported(const std::string& stmt) {
  ElabFixture f;
  std::string src = StaticMethodThisSrc(stmt);
  ElabOk(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'this' and 'super' shall not be used in a static method",
                    LineHolding(src, "static task"), "8.10"));
}

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword`, whose
// statements Parser::ParseBlockVarDecls in src/parser/parser_stmt_block.cpp
// puts in Stmt::fork_stmts.
TEST(StaticMethodThisPositions, ThisInAForkArmIsReported) {
  ExpectThisReported(
      "fork\n"
      "      k = this.x;\n"
      "    join");
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`, and
// the right-hand side of such an assignment is an ordinary expression, so it
// may name the handle. The loop's control variable is declared above the loop,
// which leaves the header's assignment as the only `this` in the source.
TEST(StaticMethodThisPositions, ThisInAForInitializationIsReported) {
  ExpectThisReported("for (k = this.x; k < 2; k = k + 1) ;");
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, and an operator_assignment
// takes the same expression on its right.
TEST(StaticMethodThisPositions, ThisInAForStepIsReported) {
  ExpectThisReported("for (k = 0; k < 2; k = this.x) ;");
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// which the parser keeps in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt.
// This case and the one below it cover one arm each.
TEST(StaticMethodThisPositions, ThisInAnAssertionPassStmtIsReported) {
  ExpectThisReported("assert (1) k = this.x;");
}

TEST(StaticMethodThisPositions, ThisInAnAssertionFailStmtIsReported) {
  ExpectThisReported("assert (1) else k = this.x;");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §8.10 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(StaticMethodThisPositions, ThisInARandcaseItemIsReported) {
  ExpectThisReported(
      "randcase\n"
      "      1 : k = this.x;\n"
      "    endcase");
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, which Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp puts
// in RsProd::code_stmts, reached through Stmt::rs_productions and through no
// other member of Stmt.
TEST(StaticMethodThisPositions, ThisInARandsequenceCodeBlockIsReported) {
  ExpectThisReported(
      "randsequence(main)\n"
      "      main : { k = this.x; };\n"
      "    endsequence");
}

// A.6.12's `rs_rule ::= rs_production_list [ := weight_specification [
// rs_code_block ] ]` puts a second code block after the weight, which the
// parser keeps in RsRule::weight_code rather than in RsProd::code_stmts. It is
// a second statement position under Stmt::rs_productions, so it takes its own
// case: the production `alt` holds a null statement, which leaves the weight
// block as the only place the handle stands.
TEST(StaticMethodThisPositions, ThisInARandsequenceWeightCodeBlockIsReported) {
  ExpectThisReported(
      "randsequence(main)\n"
      "      main : alt := 5 { k = this.x; };\n"
      "      alt : { ; };\n"
      "    endsequence");
}

// `super` stands in the same positions as `this` and is the same half of the
// sentence: ExprRefsThisOrSuper answers for both names and
// CheckStaticMethodsForThisSuper makes one report for either. One case carries
// it, in the link the walk reached last, so the conversion is not read as
// covering `this` alone.
TEST(StaticMethodThisPositions, SuperInAForkArmIsReported) {
  ElabFixture f;
  std::string src =
      "class Base;\n"
      "  function void foo(); endfunction\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  static task t();\n"
      "    fork\n"
      "      super.foo();\n"
      "    join\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  Derived d;\n"
      "endmodule\n";
  ElabOk(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'this' and 'super' shall not be used in a static method",
                    LineHolding(src, "static task"), "8.10"));
}

// The cases below are the member accesses §8.10 does not bar: a member read
// through a handle. §8.10 (printed page 186 of IEEE 1800-2023) denies a
// static method the non-static members of an object it holds no handle to, and
// §8.4 (printed 181-182) reads a member through any handle a variable holds --
// `p.fileID` in §8.9's example on the same page as §8.10 -- which a static
// method may hold as any subroutine may. ExprRefsNonStaticMember in
// src/elaborator/elaborator_validate_static_methods.cpp searched the member
// name of every `.` access as if it stood bare, so `return m_inst.k;` through a
// static property of the class and `return c.k;` through a local handle were
// each reported as the access §8.10 bars, and so was every method called
// through a handle.
//
// The class gives the static function every kind of handle the access may be
// written through: the static property `m_inst`, the local `c`, the formal
// `formal`, the static function `make` for a call's result and the local array
// `arr` for an element. `k` and `get` are the non-static members the bare
// access names, and `kid` is a non-static handle so a case can show the base
// of an access is still searched when it is the bare member.
std::string StaticMethodHandleSrc(const std::string& stmt) {
  return "class C;\n"
         "  int k = 9;\n"
         "  C kid;\n"
         "  static C m_inst;\n"
         "  function int get(); return k; endfunction\n"
         "  static function C make();\n"
         "    C h;\n"
         "    h = new;\n"
         "    return h;\n"
         "  endfunction\n"
         "  static function int f(C formal);\n"
         "    C c;\n"
         "    C arr[2];\n"
         "    " +
         stmt +
         "\n"
         "  endfunction\n"
         "endclass\n"
         "module m;\n"
         "  C c;\n"
         "endmodule\n";
}

void ExpectHandleAccessAccepted(const std::string& stmt) {
  EXPECT_TRUE(ElabOk(StaticMethodHandleSrc(stmt)));
}

// The report stands at the static function's own declaration rather than at
// the statement holding the access, because §8.10's rule is about the method:
// Elaborator::ValidateOneClassStaticMethods scans a static method body and
// reports the method once. `src` declares that function as `f`; `make` in
// StaticMethodHandleSrc is a static function of the same class and is clean,
// so the line names `f` and not the class's first method.
void ExpectStaticFunctionFReported(const std::string& src) {
  ElabFixture f;
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "static method shall not access non-static members",
                            LineHolding(src, "static function int f"), "8.10"));
}

void ExpectBareAccessReported(const std::string& stmt) {
  ExpectStaticFunctionFReported(StaticMethodHandleSrc(stmt));
}

// The shape found first: §8.9 (printed page 186) holds a static property in
// one copy shared by every object, and a handle held there is read through as
// any handle is.
TEST(StaticMethodHandleBases, PropertyThroughAStaticPropertyIsAccepted) {
  ExpectHandleAccessAccepted("return m_inst.k;");
}

TEST(StaticMethodHandleBases, PropertyThroughALocalHandleIsAccepted) {
  ExpectHandleAccessAccepted("return c.k;");
}

TEST(StaticMethodHandleBases, PropertyThroughAFormalIsAccepted) {
  ExpectHandleAccessAccepted("return formal.k;");
}

TEST(StaticMethodHandleBases, PropertyThroughACallResultIsAccepted) {
  ExpectHandleAccessAccepted("return make().k;");
}

TEST(StaticMethodHandleBases, PropertyThroughAnArrayElementIsAccepted) {
  ExpectHandleAccessAccepted("return arr[0].k;");
}

// A chain: `kid` is a non-static member, but written behind `m_inst.` it is
// read through the static property's handle and not through the object the
// static method does not have.
TEST(StaticMethodHandleBases, PropertyThroughAChainedHandleIsAccepted) {
  ExpectHandleAccessAccepted("return m_inst.kid.k;");
}

// The access as an assignment target: Stmt::lhs holds the member access, and
// the search reads its left side there as it does on the right.
TEST(StaticMethodHandleBases, PropertyAssignedThroughALocalHandleIsAccepted) {
  ExpectHandleAccessAccepted("c.k = 1; return 0;");
}

// §8.6 (printed page 183) calls a method through a handle as §8.4 reads a
// property through one; the parser keeps the call's member access in
// Expr::lhs, and a call written that way carries no bare callee.
TEST(StaticMethodHandleBases, MethodThroughAStaticPropertyIsAccepted) {
  ExpectHandleAccessAccepted("return m_inst.get();");
}

TEST(StaticMethodHandleBases, MethodThroughALocalHandleIsAccepted) {
  ExpectHandleAccessAccepted("return c.get();");
}

TEST(StaticMethodHandleBases, MethodThroughACallResultIsAccepted) {
  ExpectHandleAccessAccepted("return make().get();");
}

TEST(StaticMethodHandleBases, MethodThroughAnArrayElementIsAccepted) {
  ExpectHandleAccessAccepted("return arr[1].get();");
}

// The four cases below are the accesses §8.10 does bar, written into the same
// class so the pair with the cases above is what tells the searched side apart:
// the bare property, the bare method call, the member behind `this`, and a
// member whose base is itself a bare non-static property, which is the access
// the search of the left side still finds.
TEST(StaticMethodHandleBases, BarePropertyBesideTheHandlesIsReported) {
  ExpectBareAccessReported("return k;");
}

TEST(StaticMethodHandleBases, BareMethodCallBesideTheHandlesIsReported) {
  ExpectBareAccessReported("return get();");
}

// `this` is the one base that is no handle a static method holds, so the member
// behind it is the bare access still; CheckStaticMethodsForThisSuper reports
// the handle itself beside this report.
TEST(StaticMethodHandleBases, PropertyBehindThisIsReported) {
  ExpectBareAccessReported("return this.k;");
}

TEST(StaticMethodHandleBases, PropertyThroughABareNonStaticHandleIsReported) {
  ExpectBareAccessReported("return kid.k;");
}

// The cases below hold the same class in a package. §26.2 (printed page 808 of
// IEEE 1800-2023) makes a class declaration written in a package an item
// of that package, and §8.10 (printed 186) states its rule of the class and not
// of where the class is declared. Elaborator::ValidateStaticMethodBodies in
// src/elaborator/elaborator_validate_static_methods.cpp walked the compilation
// unit's classes and the module's own, so a package class's static method
// reading a bare non-static property was never reported, whether or not a
// module imported the package, while the same class at the top of the file
// was.
//
// `k` is the non-static property the bare access names and `m_inst` the static
// handle the accepted form reads it through, as in StaticMethodHandleSrc. The
// class is written once here and stands in a package below and in a program
// and an interface in DesignElementStaticMethodSrc.
std::string ClassCWithStaticF(const std::string& stmt) {
  return "  class C;\n"
         "    int k = 9;\n"
         "    static C m_inst;\n"
         "    static function int f();\n"
         "      " +
         stmt +
         "\n"
         "    endfunction\n"
         "  endclass\n";
}

std::string PackageStaticMethodSrc(const std::string& stmt, bool imports) {
  return "package p;\n" + ClassCWithStaticF(stmt) +
         "endpackage\n"
         "module m;\n" +
         std::string(imports ? "  import p::*;\n  C c;\n" : "") + "endmodule\n";
}

// The report stands at the static function's own declaration, as
// ExpectBareAccessReported reads it, and `f` is the class's one method.
void ExpectPackageBareAccessReported(bool imports) {
  ExpectStaticFunctionFReported(PackageStaticMethodSrc("return k;", imports));
}

TEST(StaticMethodInPackage, BarePropertyIsReportedWhereAModuleImportsIt) {
  ExpectPackageBareAccessReported(true);
}

// No module imports the package, so the class is in no module's scope at all;
// §26.2 makes it the package's item either way.
TEST(StaticMethodInPackage, BarePropertyIsReportedWhereNoModuleImportsIt) {
  ExpectPackageBareAccessReported(false);
}

// The exemption StaticMethodHandleBases states, kept for a package class: the
// property behind the static handle is read through that handle.
TEST(StaticMethodInPackage, PropertyThroughAStaticPropertyIsAccepted) {
  EXPECT_TRUE(ElabOk(PackageStaticMethodSrc("return m_inst.k;", true)));
}

// The cases below hold the class inside another class. §8.23 (printed pages
// 200-201 of IEEE 1800-2023) lets a class declare a class inside itself,
// named from outside as `Outer::Inner`, and §8.10 (printed 186) states its rule
// of a class's static method wherever the class is declared.
// Elaborator::ValidateStaticMethodsAmong in
// src/elaborator/elaborator_validate_static_methods.cpp read the direct class
// items of the compilation unit, the module and each package, so a class
// nested in any of the three was never walked and its static method reading a
// bare non-static property was never reported.
//
// `k` is the non-static property the bare access names and `m_inst` the static
// handle the accepted form reads it through, as in StaticMethodHandleSrc;
// `Inner` is the one class holding a method, so `f` is the line the report
// names.
std::string NestedClassSrc(const std::string& stmt) {
  return "class Outer;\n"
         "  class Inner;\n"
         "    int k = 9;\n"
         "    static Inner m_inst;\n"
         "    static function int f();\n"
         "      " +
         stmt +
         "\n"
         "    endfunction\n"
         "  endclass\n"
         "endclass\n";
}

// The outer class at the top of the file, inside the module, or inside a
// package, which are the three item lists the walk reads.
std::string NestedUnitClassSrc(const std::string& stmt) {
  return NestedClassSrc(stmt) + "module m;\nendmodule\n";
}

std::string NestedModuleClassSrc(const std::string& stmt) {
  return "module m;\n" + NestedClassSrc(stmt) + "endmodule\n";
}

std::string NestedPackageClassSrc(const std::string& stmt) {
  return "package p;\n" + NestedClassSrc(stmt) +
         "endpackage\n"
         "module m;\n"
         "  import p::*;\n"
         "endmodule\n";
}

TEST(StaticMethodInNestedClass, BarePropertyIsReportedInAUnitClass) {
  ExpectStaticFunctionFReported(NestedUnitClassSrc("return k;"));
}

TEST(StaticMethodInNestedClass, BarePropertyIsReportedInAModuleClass) {
  ExpectStaticFunctionFReported(NestedModuleClassSrc("return k;"));
}

TEST(StaticMethodInNestedClass, BarePropertyIsReportedInAPackageClass) {
  ExpectStaticFunctionFReported(NestedPackageClassSrc("return k;"));
}

// The exemption StaticMethodHandleBases states, kept for a nested class: the
// property behind the static handle is read through that handle, so a walk
// that reported every nested static method is told from one reading the body.
TEST(StaticMethodInNestedClass, PropertyThroughAStaticPropertyIsAccepted) {
  EXPECT_TRUE(ElabOk(NestedUnitClassSrc("return m_inst.k;")));
  EXPECT_TRUE(ElabOk(NestedPackageClassSrc("return m_inst.k;")));
}

// The cases below hold the class in a program or an interface that nothing
// instantiates. §24.3 (printed page 775 of IEEE 1800-2023) admits a class
// declaration among a program's items and §25.3 (printed 781) among an
// interface's; §17.2 (printed 503-504) names none among a checker's, and the
// parser reports one there under A.1.8 (test_parser_annex_a_01_08.cpp), so no
// checker case stands here. §8.10 (printed 186) states its rule of the class
// wherever it is declared. Elaborator::ValidateStaticMethodBodies in
// src/elaborator/elaborator_validate_static_methods.cpp read the items of the
// module it was run for, and it is run for a program or an interface only when
// that one is elaborated -- instantiated, or a program rooted as a top -- so
// the class of one that was neither was never walked.
//
// `module m` stands after the element and is the top the fixture names, so
// the element is elaborated by no run; a program alone in the file would be
// rooted as a top per §24.3 and reach the module walk, and the case would
// pass on the walk that was already there. `element` is the keyword that
// opens the declaration, and `end` + `element` closes it.
std::string DesignElementStaticMethodSrc(const std::string& element,
                                         const std::string& stmt) {
  return element + " e;\n" + ClassCWithStaticF(stmt) + "end" + element +
         "\n"
         "module m;\n"
         "endmodule\n";
}

TEST(StaticMethodInDesignElement, BarePropertyIsReportedInAProgram) {
  ExpectStaticFunctionFReported(
      DesignElementStaticMethodSrc("program", "return k;"));
}

TEST(StaticMethodInDesignElement, BarePropertyIsReportedInAnInterface) {
  ExpectStaticFunctionFReported(
      DesignElementStaticMethodSrc("interface", "return k;"));
}

// The exemption StaticMethodHandleBases states, kept for a class an
// uninstantiated element holds: the property behind the static handle is read
// through that handle, so a walk that reported every such static method is
// told from one reading the body.
TEST(StaticMethodInDesignElement, PropertyThroughAStaticPropertyIsAccepted) {
  EXPECT_TRUE(
      ElabOk(DesignElementStaticMethodSrc("interface", "return m_inst.k;")));
}

}  // namespace
