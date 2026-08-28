#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(ClassScopeResolutionElaboration, ScopeResolutionTypedefOk) {
  EXPECT_TRUE(
      ElabOk("class Cfg;\n"
             "  typedef int my_type;\n"
             "endclass\n"
             "module m;\n"
             "  Cfg::my_type x;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, ScopeResolutionStaticMethodOk) {
  EXPECT_TRUE(
      ElabOk("class Utils;\n"
             "  static function void compute();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial Utils::compute();\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, ScopeResolutionParameterOk) {
  EXPECT_TRUE(
      ElabOk("class Cfg;\n"
             "  parameter int WIDTH = 8;\n"
             "endclass\n"
             "module m;\n"
             "  logic [Cfg::WIDTH-1:0] data;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, NestedClassDeclOk) {
  EXPECT_TRUE(
      ElabOk("class Outer;\n"
             "  class Inner;\n"
             "    int val;\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, SuperclassScopeAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  static int count;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int get_count();\n"
             "    return Base::count;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, StaticPropertyReadOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static int count;\n"
             "endclass\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = C::count;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, EnumAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  typedef enum {bin, oct, dec, hex} radix;\n"
             "endclass\n"
             "module m;\n"
             "  int x;\n"
             "  initial x = Base::bin;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, ChainedScopeOk) {
  EXPECT_TRUE(
      ElabOk("class Outer;\n"
             "  class Inner;\n"
             "    static int x;\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "  int y;\n"
             "  initial y = Outer::Inner::x;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, LocalparamAccessOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  localparam int SIZE = 16;\n"
             "endclass\n"
             "module m;\n"
             "  logic [C::SIZE-1:0] data;\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, DisambiguationOk) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  typedef enum {bin, oct, dec, hex} radix;\n"
             "  static task print(radix r, integer n);\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  int bin = 123;\n"
             "  initial Base::print(Base::bin, bin);\n"
             "endmodule\n"));
}

TEST(ClassScopeResolutionElaboration, NestedClassAsTypeOk) {
  EXPECT_TRUE(
      ElabOk("class StringList;\n"
             "  class Node;\n"
             "    string name;\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "  StringList::Node n;\n"
             "endmodule\n"));
}

// §8.23: while a type parameter may resolve to a class type, use of the class
// scope resolution operator to select something through such a prefix is
// restricted to typedef declarations, the type operator, and type parameter
// assignments. A type parameter prefixing '::' in an expression is outside the
// permitted contexts and must be reported. §6.20.3 states the type parameter
// case in its own words, so this leg is reported under that subclause and must
// stay there: extending the check to the other two prefix kinds §8.23 names,
// the incomplete forward type and the interface-based typedef, must not move
// the type parameter report to §8.23.
TEST(ClassScopeResolutionElaboration, TypeParamScopePrefixRestricted) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  static int val = 7;\n"
      "endclass\n"
      "module m;\n"
      "  parameter type T = C;\n"
      "  int x;\n"
      "  initial x = T::val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type parameter 'T' may prefix the class scope resolution operator", 7,
      "6.20.3"));
}

// §8.23: the same restriction holds when the type parameter comes from the
// parameter port list and the '::' prefix appears inside a procedural always
// block (here on the right side of a nonblocking assignment), confirming the
// restriction is enforced across these contexts rather than only in an initial
// block with a body-declared type parameter. §6.20.3 states the type parameter
// case in its own words, so this leg is reported under that subclause and must
// stay there when the check grows the two prefix kinds §8.23 adds.
TEST(ClassScopeResolutionElaboration,
     PortTypeParamScopePrefixInAlwaysBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  logic clk;\n"
      "  logic q;\n"
      "  always @(posedge clk) q <= T::n;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type parameter 'T' may prefix the class scope resolution operator", 4,
      "6.20.3"));
}

// §8.23: an incomplete forward type is one of the three prefix kinds whose use
// with the class scope resolution operator is confined to a typedef
// declaration, the type operator, and a type parameter assignment. A forward
// type no definition in the scope completes is incomplete, so prefixing '::'
// with it in an expression is outside all three and is reported under §8.23.
TEST(ClassScopeResolutionElaboration, IncompleteForwardTypePrefixIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial x = C::val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    4, "8.23"));
}

// §8.23: a type defined by an interface-based typedef, the §6.18 form that
// names a type through an interface port, is the third restricted prefix kind.
// Selecting through it in an expression is none of the three permitted
// contexts and is reported under §8.23.
TEST(ClassScopeResolutionElaboration, InterfaceBasedTypedefPrefixIsError) {
  ElabFixture f;
  ElaborateSrc(
      "interface intf_i;\n"
      "  typedef int data_t;\n"
      "endinterface\n"
      "module sub(intf_i p);\n"
      "  typedef p.data_t my_data_t;\n"
      "  int x;\n"
      "  initial x = my_data_t::val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type 'my_data_t' defined by an interface-based typedef", 7, "8.23"));
}

// §8.23 restricts an *incomplete* forward type, and §6.18 lets the definition
// that completes one appear before or after the forward declaration. A forward
// type a class in the scope resolves is therefore an ordinary class type name,
// and prefixing '::' with it in an expression stays legal. This guards the
// §8.23 check against rejecting the forward-declaration pattern §6.18 makes
// legal in either order.
TEST(ClassScopeResolutionElaboration, ResolvedForwardTypePrefixOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static int val = 7;\n"
             "endclass\n"
             "module m;\n"
             "  typedef class C;\n"
             "  int x;\n"
             "  initial x = C::val;\n"
             "endmodule\n"));
}

// §8.23: a typedef declaration is the first of the three contexts in which a
// restricted prefix may precede the class scope resolution operator, so
// selecting a type out of a forward-declared class inside a typedef
// elaborates.
TEST(ClassScopeResolutionElaboration, ForwardTypePrefixInTypedefDeclOk) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  typedef class Frame;\n"
             "  class Frame;\n"
             "    typedef byte payload_t;\n"
             "  endclass\n"
             "  typedef Frame::payload_t alias_t;\n"
             "endmodule\n"));
}

// §8.23: a type parameter assignment is the third context in which a restricted
// prefix may precede the class scope resolution operator. §6.20.3 writes that
// context as `localparam type C_t = C::T;` in the example it states the rule
// with, so selecting a type out of a forward-declared class as the default of a
// type parameter elaborates. The default is parsed into `typedef_type` rather
// than into an expression, which is why the expression walk that reports the
// restriction never reaches it.
TEST(ClassScopeResolutionElaboration,
     ForwardTypePrefixInTypeParamAssignmentOk) {
  EXPECT_TRUE(
      ElabOk("module box;\n"
             "  typedef class Packet;\n"
             "  class Packet;\n"
             "    typedef shortint stamp_t;\n"
             "  endclass\n"
             "  localparam type stamp_alias_t = Packet::stamp_t;\n"
             "endmodule\n"));
}

// §6.18: a forward-declared name completed by something other than a class
// cannot carry a scope-resolution prefix at all, whichever context the prefix
// stands in. That report belongs to §6.18 and is the neighbour of the §8.23
// check: a typedef declaration is a permitted §8.23 context, so the source
// below must still be rejected, and by §6.18.
TEST(ClassScopeResolutionElaboration, NonClassForwardPrefixInTypedefIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module w;\n"
      "  typedef pkt_fwd;\n"
      "  typedef byte pkt_fwd;\n"
      "  typedef pkt_fwd::Field field_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "scope-resolution prefix", 4,
                            "6.18"));
}

// §8.23: an ordinary class type name remains a valid scope resolution prefix in
// an expression; the restriction applies only to a type parameter prefix.
TEST(ClassScopeResolutionElaboration, ClassNamePrefixInExpressionOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static int val = 7;\n"
             "endclass\n"
             "module m;\n"
             "  parameter type T = int;\n"
             "  T data;\n"
             "  int x;\n"
             "  initial x = C::val;\n"
             "endmodule\n"));
}

// §8.23: a class-scoped parameter is a constant expression. Referencing it via
// `Class::PARAM` in a constant context must fold to the parameter's value at
// elaboration, not merely elaborate without error. Cfg::WIDTH resolves to 8.
TEST(ClassScopeResolutionElaboration, ClassParameterFoldsAsConstant) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Cfg;\n"
      "  parameter int WIDTH = 8;\n"
      "endclass\n"
      "module m;\n"
      "  localparam int W = Cfg::WIDTH;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->params[0].name, "W");
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 8);
}

// §8.23: a class-scoped local parameter is likewise a constant expression
// reachable through `::`. Cfg::DEPTH resolves to 16.
TEST(ClassScopeResolutionElaboration, ClassLocalparamFoldsAsConstant) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Cfg;\n"
      "  localparam int DEPTH = 16;\n"
      "endclass\n"
      "module m;\n"
      "  localparam int D = Cfg::DEPTH;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->params[0].name, "D");
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 16);
}

// §8.23: an incomplete forward type may prefix the class scope resolution
// operator only within a typedef declaration, the type operator, or a type
// parameter assignment, and a data object declaration is none of the three, so
// `C::T x;` is rejected under §8.23. IncompleteForwardTypePrefixIsError above
// covers the same prefix where an expression carries it; here the prefix
// reaches the elaborator through DataType::scope_name on the declared type
// instead. No class completes `C`, because §6.18 makes a forward type a
// complete type once a definition resolves it and ResolvedForwardTypePrefixOk
// above pins that a resolved prefix stays legal: a completing class would
// leave nothing incomplete for this report to name. The §6.18 reports the
// unresolved name also provokes are separated from this one by the message and
// the subclause asserted here rather than by the source.
TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInDataDeclIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  C::T x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    3, "8.23"));
}

// §8.23: a type defined by an interface-based typedef, the §6.18 form naming a
// type through an interface port, may prefix the class scope resolution
// operator only within a typedef declaration, the type operator, or a type
// parameter assignment. A data object declaration is none of the three, so the
// declaration of `x` is rejected under §8.23.
// InterfaceBasedTypedefPrefixIsError above asserts the same report where an
// expression carries the prefix, and uses the same interface and typedef this
// case declares.
TEST(ClassScopeResolutionElaboration,
     InterfaceBasedTypedefPrefixInDataDeclIsError) {
  ElabFixture f;
  ElaborateSrc(
      "interface intf_i;\n"
      "  typedef int data_t;\n"
      "endinterface\n"
      "module sub(intf_i p);\n"
      "  typedef p.data_t my_data_t;\n"
      "  my_data_t::Field x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type 'my_data_t' defined by an interface-based typedef", 6, "8.23"));
}

// §6.20.3 gives `class P#(type C); C::T x;` as its worked illegal example
// (~/LRM.pdf PDF page 129, printed 128), marking the property declaration
// "Illegal, C is an incomplete type". The prefix is a type parameter and a
// class property declaration is none of the three contexts §8.23 permits, so
// the report names §6.20.3, the subclause that states the type parameter case
// in its own words. The prefix stands on a class member rather than on a
// module item, which is what separates this case from the module-scope form.
TEST(ClassScopeResolutionElaboration, TypeParamPrefixInClassPropertyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class P #(type C);\n"
      "  C::T x;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type parameter 'C' may prefix the class scope resolution operator", 2,
      "6.20.3"));
}

// §6.20.3 marks the other half of that same example legal: `localparam type
// C_t = C::T;` reaches `C::T` by a type parameter assignment, which §8.23
// permits, and `C_t y;` then declares the property through an ordinary type
// name carrying no prefix. Both must elaborate, so a check that rejected every
// class property whose type is written with a scope prefix is caught here
// rather than passing on TypeParamPrefixInClassPropertyIsError alone.
TEST(ClassScopeResolutionElaboration,
     ClassPropertyThroughTypeParamAssignmentOk) {
  EXPECT_TRUE(
      ElabOk("class P #(type C);\n"
             "  localparam type C_t = C::T;\n"
             "  C_t y;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §6.18: a forward-declared name completed by something other than a class
// cannot carry a scope-resolution prefix, and a type parameter assignment is a
// context §8.23 permits the prefix in, so the permission does not save this
// source. `pkt_fwd` is completed by `byte`, so the prefix does not resolve to a
// class and the assignment is rejected under §6.18.
// NonClassForwardPrefixInTypedefIsError above asserts the same rule for the
// `typedef` spelling of the same rejection, and the two differ only in the
// construct the prefix is written on.
TEST(ClassScopeResolutionElaboration,
     NonClassForwardPrefixInTypeParamAssignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module w;\n"
      "  typedef pkt_fwd;\n"
      "  typedef byte pkt_fwd;\n"
      "  localparam type field_t = pkt_fwd::Field;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "scope-resolution prefix 'pkt_fwd' of a type parameter assignment", 4,
      "6.18"));
}

// §8.23 (printed page 200): "Because classes and other scopes can have the same
// identifiers, the class scope resolution operator uniquely identifies a
// member, a parameter or local parameter of a particular class", which the
// clause writes out as `b.print( Base::bin, bin );  // Base::bin and bin are
// different`. The two my_type declarations below therefore have to differ in
// width, or the case passes whether the prefix was read or dropped: 32 is the
// int inside Cfg, and the module's byte would answer 8.
//
// The widths are read back rather than elaboration being asserted to succeed,
// because nothing reports a named type that resolved to nothing. EvalTypeWidth
// at src/elaborator/type_eval.cpp answers 0 for an unresolved
// DataTypeKind::kNamed and the run carries on, so ScopeResolutionTypedefOk
// above holds however the lookup went.
TEST(ClassScopeResolutionElaboration, ScopedTypedefSizesFromTheNamedClass) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Cfg;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m;\n"
      "  typedef byte my_type;\n"
      "  Cfg::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* x = FindVar(design, "m", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 32u);
}

// The same declaration with no unqualified my_type anywhere, which is
// ScopeResolutionTypedefOk's source read back. It separates a prefix that
// resolves from one that finds nothing: 32 is Cfg's int, and a lookup that
// missed would leave x at the 0 an unresolved kNamed evaluates to.
TEST(ClassScopeResolutionElaboration, ScopedTypedefSizesWithNoUnqualifiedName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Cfg;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m;\n"
      "  Cfg::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* x = FindVar(design, "m", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 32u);
}

// The seven cases below cover the child-statement links of Stmt that
// WalkStmtsForRestrictedScopePrefix in
// src/elaborator/elaborator_validate_classes.cpp reaches for the first time now
// that it takes its list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. It had written out six of the
// thirteen, so a restricted prefix standing in any of the other seven reached
// CheckRestrictedScopePrefixExpr through no link and was left unreported. Each
// case writes the prefix kind IncompleteForwardTypePrefixIsError above uses,
// because the three contexts §8.23 permits are parsed as data types and never
// as expressions, which puts a prefix reached from a statement outside the
// permitted set wherever that statement stands. The report is at the prefix
// itself, the `C` of `C::val`.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, so a fork arm
// holds the expression like any other statement position.
TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInForkArmIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial fork\n"
      "    x = C::val;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    5, "8.23"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`, so
// the right-hand side of a header assignment is an ordinary expression. The
// loop's control variable is declared above the loop, which leaves the header
// as the only place the prefix is written.
TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInForInitializationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (x = C::val; i < 2; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    5, "8.23"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, so a for step carries an
// expression the same way.
TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInForStepIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 2; x = C::val) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    5, "8.23"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm.
// Which arm runs is settled when the design runs, and §8.23 restricts where the
// prefix may be written.
TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInAssertionPassStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial assert (1) x = C::val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    4, "8.23"));
}

TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInAssertionFailStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial assert (1) else x = C::val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    4, "8.23"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. The item is reported whether the weighted draw would select it or
// not.
TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInRandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : x = C::val;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    6, "8.23"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp
// puts them in RsProd::code_stmts, which Stmt::rs_productions reaches and no
// other member of Stmt does.
TEST(ClassScopeResolutionElaboration,
     IncompleteForwardTypePrefixInRandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef class C;\n"
      "  int x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = C::val; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "incomplete forward type 'C' may prefix the class scope "
                    "resolution operator",
                    6, "8.23"));
}

}  // namespace
