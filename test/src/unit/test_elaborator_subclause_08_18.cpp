#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DataHidingElaboration, PublicMemberAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.x = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalMemberAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.secret = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            8, "8.18"));
}

TEST(DataHidingElaboration, ProtectedMemberAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  protected int hidden;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.hidden = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access protected member from outside", 8,
                            "8.18"));
}

TEST(DataHidingElaboration, LocalMethodAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local function int get_id();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.get_id();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            10, "8.18"));
}

TEST(DataHidingElaboration, PublicMethodAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  function void show(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.show();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ProtectedMethodAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  protected function void secret(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.secret();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access protected member from outside", 8,
                            "8.18"));
}

TEST(DataHidingElaboration, ConstructorLocalAllowed) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  local function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ConstructorProtectedAllowed) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  protected function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// §8.18: local members are not visible within subclasses.
// A base-class local accessed through a derived handle is still rejected.
TEST(DataHidingElaboration, LocalNotVisibleViaDerivedHandle) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  local int secret;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    d.secret = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            10, "8.18"));
}

// §8.18: a protected member has all the characteristics of a local member
// except that it is inherited / visible to subclasses. A subclass method
// may reference an inherited protected property.
TEST(DataHidingElaboration, ProtectedAccessibleInSubclassMethod) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  protected int hidden;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int read_hidden();\n"
             "    return hidden;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// §8.18: the visible-to-subclasses characteristic of a protected member applies
// to methods as well as properties. A subclass method may call an inherited
// protected method — the method form of the preceding property test.
TEST(DataHidingElaboration, ProtectedMethodAccessibleInSubclassMethod) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  protected function int secret();\n"
             "    return 7;\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int reveal();\n"
             "    return secret();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// §8.18: within a class, a local property of the same class may be
// referenced even if it is in a different instance of the same class.
TEST(DataHidingElaboration, SameClassInstanceLocalAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int i;\n"
             "  function int compare(Packet other);\n"
             "    return (this.i == other.i);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

// §8.18: a protected member has all the characteristics of a local member
// (differing only in being inheritable). The same-class cross-instance
// reference permitted for a local property is therefore equally permitted for a
// protected one: a method may read a protected property of another instance of
// its own class.
TEST(DataHidingElaboration, SameClassInstanceProtectedAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  protected int i;\n"
             "  function int compare(Packet other);\n"
             "    return (this.i == other.i);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

// The twelve cases below cover the child-statement links of Stmt that the
// §8.18 walk in src/elaborator/elaborator_validate_classes.cpp reaches for the
// first time now that WalkStmtsForVisibility and CollectBlockClassVarDecls both
// take their list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Each had written out six of
// the thirteen links, so an access in a link the walk was missing was never
// examined, and a handle declared in a link the collection was missing was
// never recorded with the class it was declared as.
//
// Each link a declaration can stand in takes a pair. The rejected case writes
// the access through the module-scope handle `p`, which the walk has to reach.
// The accepted case redeclares `p` in the same link as a handle to a class
// whose `secret` is public, so the access is legal and §8.18 has nothing to
// report.
//
// The accepted case guards that outcome rather than isolating the collection.
// Elaborator::ValidateClassHandleOps in
// src/elaborator/elaborator_validate_class_handles.cpp already descends all
// thirteen links, it stands earlier in the ordered series
// Elaborator::ValidateModuleConstraints runs, and it records every block-local
// handle in Elaborator::class_var_types_ -- the map CollectBlockClassVarDecls
// is seeded from -- so the redeclaration reaches the §8.18 pass whatever the
// collection itself reaches. No case here can therefore separate the two
// walks, and the collection is converted because §8.18 is one rule and reading
// its two halves off two different lists is what put the reporter and the
// collector out of step to begin with.

// §8.18 states that a local member is unreachable from outside its class and
// puts no condition on the statement the access is written in. A.6.3 gives
// `par_block ::= fork [ : block_identifier ] { block_item_declaration } {
// statement_or_null } join_keyword`, so a fork arm holds both halves of this
// pair directly: the assignment here, and the declaration in the case below it,
// which Parser::ParseBlockVarDecls in src/parser/parser_stmt_block.cpp puts in
// Stmt::fork_stmts beside the statements.
TEST(DataHidingElaboration, LocalMemberAccessInAForkArmIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial fork\n"
      "    p.secret = 1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            7, "8.18"));
}

TEST(DataHidingElaboration, HandleRedeclaredInAForkArmChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial fork\n"
             "    Open p;\n"
             "    p.secret = 1;\n"
             "  join\n"
             "endmodule\n"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// `variable_assignment ::= variable_lvalue = expression`, and A.8.5 makes a
// member select a variable_lvalue, so a for header assigns through a class
// handle. The loop's control variable is declared above the loop, which leaves
// the header's assignment as the only access in the source.
//
// The link takes the rejected case alone. A for_variable_declaration is not a
// data_declaration and Parser::ParseForLocalDeclInits in
// src/parser/parser_stmt.cpp records it in Stmt::for_init_types beside the
// assignment, so no declaration statement ever stands in Stmt::for_inits for
// CollectBlockClassVarDecls to read.
TEST(DataHidingElaboration, LocalMemberAccessInAForInitializationIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  int i;\n"
      "  initial for (p.secret = 0; i < 2; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            7, "8.18"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, so a for step writes
// through a class handle the same way. None of the three declares a name, so
// this link takes the rejected case alone.
TEST(DataHidingElaboration, LocalMemberAccessInAForStepIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 2; p.secret = 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            7, "8.18"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// which Parser::ParseAssertStmt in src/parser/parser_assert.cpp puts in
// Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. A declaration is not a
// statement_or_null, so the accepted case of each pair writes its declaration
// inside a begin-end block the arm holds.
TEST(DataHidingElaboration, LocalMemberAccessInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial assert (1) p.secret = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            6, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInAnAssertionPassStmtChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial assert (1) begin\n"
             "    Open p;\n"
             "    p.secret = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalMemberAccessInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial assert (1) else p.secret = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            6, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInAnAssertionFailStmtChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial assert (1) else begin\n"
             "    Open p;\n"
             "    p.secret = 1;\n"
             "  end\n"
             "endmodule\n"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §8.18 is a rule about the source, so it holds whether the weighted
// draw would select the item or not, and the declaration again needs the
// begin-end block a statement_or_null admits.
TEST(DataHidingElaboration, LocalMemberAccessInARandcaseItemIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : p.secret = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            8, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInARandcaseItemChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    randcase\n"
             "      1 : begin\n"
             "        Open p;\n"
             "        p.secret = 1;\n"
             "      end\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds both halves of this pair
// directly. Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp puts
// them in RsProd::code_stmts, which Stmt::rs_productions reaches and no other
// member of Stmt does.
TEST(DataHidingElaboration,
     LocalMemberAccessInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { p.secret = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            8, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInARandsequenceCodeBlockChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    randsequence(main)\n"
             "      main : { Open p; p.secret = 1; };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

// §6.21 says of a declaration in a block that "These variables are visible to
// the unnamed block and any nested blocks below it", so the class a handle's
// name stands for ends where its block does. The table the checks read was a
// member written straight into and unwound by nothing, so a handle declared in
// one procedural block rebound its name for the rest of the module.
//
// Here the module declares `p` a Packet, whose member is local, and an earlier
// block declares its own `p` as an Open, whose member is not. The access in the
// second block is to the module's Packet and earns the report; the block-local
// binding outliving its block is what hid it.
TEST(DataHidingElaboration, ABlockLocalHandleDoesNotRebindTheNameAfterIt) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "class Open;\n"
      "  int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial begin\n"
      "    Open p;\n"
      "    p.secret = 1;\n"
      "  end\n"
      "  initial p.secret = 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            13, "8.18"));
}

// The other direction, which is what tells a scoped table from a merely cleared
// one: the module's handle is the Open and the block's is the Packet, so the
// access after the block earns no report and a table still holding the block's
// binding produces one the source does not deserve.
TEST(DataHidingElaboration, ABlockLocalHandleDoesNotEarnTheNameAReport) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "class Open;\n"
      "  int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Open p;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "  end\n"
      "  initial p.secret = 2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// Two sibling blocks, each declaring `p` as a different class and each reaching
// the member. Exactly one of them earns the report, so a fix that unwinds at
// the wrong grain -- once per module, or never -- is told from one that unwinds
// at the block.
TEST(DataHidingElaboration, SiblingBlocksBindTheSameNameSeparately) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "class Open;\n"
      "  int secret;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Open p;\n"
      "    p.secret = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p.secret = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            14, "8.18"));
  EXPECT_EQ(f.diag.Diagnostics().size(), 1u);
}

// The cases below reach the member through a class-scoped static handle. §8.9
// (printed page 186 of ~/IEEE 1800-2023.pdf) holds a static property in one
// copy usable with no object, reached as `C::m_inst`, and §8.4 (printed
// 181-182) reads a member through whatever handle a variable holds; §8.18
// (printed 194) confines a local member to the methods of its class and a
// protected one to the class and its subclasses, and a module's procedure is
// outside both. CheckMemberAccessVisibility in
// src/elaborator/elaborator_validate_classes.cpp read the handle's class from a
// variable's declared type alone, so `C::m_inst.k` and `p::C::m_inst.k`
// resolved to no class and a local `k` behind either was accepted where `c.k`
// through `C c;` was reported, and `C::m_inst` itself, declared `static local`,
// was accepted for the same reason: only a `.` access was ever read.
//
// `k_decl` declares the property the access reaches and `handle_decl` the
// static handle it reaches it through, so a case can qualify either one.
std::string StaticHandleClassSrc(const std::string& k_decl,
                                 const std::string& handle_decl) {
  return "class C;\n  " + k_decl + "\n  " + handle_decl + "\nendclass\n";
}

std::string StaticHandleModuleSrc(const std::string& stmt) {
  return "module m;\n  int x;\n  C c;\n  initial " + stmt + "\nendmodule\n";
}

// The report stands at the access, which the module's one initial holds.
void ExpectScopedAccessReported(const std::string& src,
                                std::string_view message) {
  ElabFixture f;
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(src, "initial"), "8.18"));
}

TEST(ScopedStaticHandleHiding, LocalMemberBehindTheStaticHandleIsReported) {
  ExpectScopedAccessReported(
      StaticHandleClassSrc("local int k = 9;", "static C m_inst;") +
          StaticHandleModuleSrc("x = C::m_inst.k;"),
      "cannot access local member from outside its class");
}

TEST(ScopedStaticHandleHiding, ProtectedMemberBehindTheStaticHandleIsReported) {
  ExpectScopedAccessReported(
      StaticHandleClassSrc("protected int k = 9;", "static C m_inst;") +
          StaticHandleModuleSrc("x = C::m_inst.k;"),
      "cannot access protected member from outside its class hierarchy");
}

// `class_src` held in a package, and a module reaching into it with `stmt`.
std::string PackageStaticHandleSrc(const std::string& class_src,
                                   const std::string& stmt) {
  return "package p;\n" + class_src +
         "endpackage\nmodule m;\n  int x;\n  initial " + stmt + "\nendmodule\n";
}

// The package form: §26.3 (printed 808) resolves `p::C` to the package's
// class, and the handle's class is read through the same static property.
TEST(ScopedStaticHandleHiding,
     LocalMemberBehindThePackageClassStaticHandleIsReported) {
  ExpectScopedAccessReported(
      PackageStaticHandleSrc(
          StaticHandleClassSrc("local int k = 9;", "static C m_inst;"),
          "x = p::C::m_inst.k;"),
      "cannot access local member from outside its class");
}

// The static handle itself, qualified: `C::m_inst` names the member with no
// object, and the qualifier holds on it as on any member.
TEST(ScopedStaticHandleHiding, LocalStaticHandleNamedByTheClassIsReported) {
  ExpectScopedAccessReported(
      StaticHandleClassSrc("int k = 9;", "static local C m_inst;") +
          StaticHandleModuleSrc("c = C::m_inst;"),
      "cannot access local member from outside its class");
}

// The pair's accepting half: a public handle's public member, which a check
// reporting every scoped access would report too.
TEST(ScopedStaticHandleHiding, PublicMemberBehindThePublicStaticHandleIsOk) {
  EXPECT_TRUE(ElabOk(StaticHandleClassSrc("int k = 9;", "static C m_inst;") +
                     StaticHandleModuleSrc("x = C::m_inst.k;")));
}

// The cases below hold the class inside another class. §8.23 (printed pages
// 200-201) lets a class declare a class inside itself, named from outside as
// `Outer::Inner` and `p::Outer::Inner` through a package, and §8.18 confines
// the nested class's local members as it confines any class's.
// ClassOfScopePrefix in src/elaborator/elaborator_validate_classes.cpp
// resolved a prefix of one identifier or a package's and a class's and nothing
// longer, so `Outer::Inner::m_inst.k` on a local `k`, `Outer::Inner::m_inst`
// on a `static local` handle and the `p::Outer::Inner` forms were each
// accepted where `C::m_inst.k` was reported.
//
// `k_decl` and `handle_decl` are the nested class's two members, as in
// StaticHandleClassSrc; the handle's type is written by its bare name, which
// §8.23 (printed 201) scopes inside the class that declares it.
std::string NestedStaticHandleClassSrc(const std::string& k_decl,
                                       const std::string& handle_decl) {
  return "class Outer;\n  class Inner;\n    " + k_decl + "\n    " +
         handle_decl + "\n  endclass\nendclass\n";
}

std::string NestedStaticHandleModuleSrc(const std::string& stmt) {
  return "module m;\n  int x;\n  Outer::Inner c;\n  initial " + stmt +
         "\nendmodule\n";
}

TEST(NestedStaticHandleHiding, LocalMemberBehindTheStaticHandleIsReported) {
  ExpectScopedAccessReported(
      NestedStaticHandleClassSrc("local int k = 9;", "static Inner m_inst;") +
          NestedStaticHandleModuleSrc("x = Outer::Inner::m_inst.k;"),
      "cannot access local member from outside its class");
}

TEST(NestedStaticHandleHiding, LocalStaticHandleNamedByTheClassIsReported) {
  ExpectScopedAccessReported(
      NestedStaticHandleClassSrc("int k = 9;", "static local Inner m_inst;") +
          NestedStaticHandleModuleSrc("c = Outer::Inner::m_inst;"),
      "cannot access local member from outside its class");
}

// The package form: §26.3 (printed 808) resolves `p::Outer` to the package's
// class, and `Inner` is read as a class nested in it from there.
TEST(NestedStaticHandleHiding,
     LocalMemberBehindThePackageClassStaticHandleIsReported) {
  ExpectScopedAccessReported(
      PackageStaticHandleSrc(NestedStaticHandleClassSrc("local int k = 9;",
                                                        "static Inner m_inst;"),
                             "x = p::Outer::Inner::m_inst.k;"),
      "cannot access local member from outside its class");
}

// The pair's accepting half: a public nested handle's public member, which a
// walk that reported every resolved nested access would report too.
TEST(NestedStaticHandleHiding, PublicMemberBehindThePublicStaticHandleIsOk) {
  EXPECT_TRUE(
      ElabOk(NestedStaticHandleClassSrc("int k = 9;", "static Inner m_inst;") +
             NestedStaticHandleModuleSrc("x = Outer::Inner::m_inst.k;")));
}

// The cases below hold the handle in one nested class and its type in a
// sibling: `class Outer; class A; local int k; endclass class B; static A a;
// endclass endclass`. §8.23 (printed 201) resolves a name written inside a
// nested class first in that class, then in each enclosing class outward, then
// the enclosing scope, so `A` inside B is Outer's nested A, and §8.18 confines
// its local `k` as any class's. ClassOfDeclaredType in
// src/elaborator/elaborator_validate_classes.cpp read a bare type name as the
// owner, a class nested in the owner or a class of the unit, and a scoped one
// as a package's class or one nested in a class of the unit, so `A` and
// `Outer::A` written inside B resolved to no class and `Outer::B::a.k` was
// accepted from a module where `Outer::Inner::m_inst.k` was reported.
//
// `k_decl` is A's one member and `handle_decl` B's; `mid_open` and `mid_close`
// wrap B in a further class for the deeper chain.
std::string SiblingStaticHandleClassSrc(const std::string& k_decl,
                                        const std::string& handle_decl,
                                        const std::string& mid_open = "",
                                        const std::string& mid_close = "") {
  return "class Outer;\n  class A;\n    " + k_decl + "\n  endclass\n" +
         mid_open + "  class B;\n    " + handle_decl + "\n  endclass\n" +
         mid_close + "endclass\n";
}

std::string SiblingStaticHandleModuleSrc(const std::string& stmt) {
  return "module m;\n  int x;\n  initial " + stmt + "\nendmodule\n";
}

TEST(SiblingStaticHandleHiding, LocalMemberBehindTheStaticHandleIsReported) {
  ExpectScopedAccessReported(
      SiblingStaticHandleClassSrc("local int k = 9;", "static A a;") +
          SiblingStaticHandleModuleSrc("x = Outer::B::a.k;"),
      "cannot access local member from outside its class");
}

// The type written through the enclosing class: `Outer::A` inside B names the
// chain element Outer and the A nested in it.
TEST(SiblingStaticHandleHiding,
     LocalMemberBehindTheScopedTypeHandleIsReported) {
  ExpectScopedAccessReported(
      SiblingStaticHandleClassSrc("local int k = 9;", "static Outer::A a;") +
          SiblingStaticHandleModuleSrc("x = Outer::B::a.k;"),
      "cannot access local member from outside its class");
}

// B two classes deep, A still nested in Outer: the walk passes Mid, which
// holds no A, and reaches Outer's.
TEST(SiblingStaticHandleHiding,
     LocalMemberBehindTheDeeperChainHandleIsReported) {
  ExpectScopedAccessReported(
      SiblingStaticHandleClassSrc("local int k = 9;", "static A a;",
                                  "  class Mid;\n", "  endclass\n") +
          SiblingStaticHandleModuleSrc("x = Outer::Mid::B::a.k;"),
      "cannot access local member from outside its class");
}

// The pair's accepting half: a public sibling's public member.
TEST(SiblingStaticHandleHiding, PublicMemberBehindThePublicStaticHandleIsOk) {
  EXPECT_TRUE(ElabOk(SiblingStaticHandleClassSrc("int k = 9;", "static A a;") +
                     SiblingStaticHandleModuleSrc("x = Outer::B::a.k;")));
}

}  // namespace
