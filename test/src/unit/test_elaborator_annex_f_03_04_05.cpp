#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

using namespace delta;

// §F.3.4.5 unfolds a local variable declaration naming k > 1 variables into
// the declaration of its first variable over the declaration of the rest,
// until each declaration names one variable, over any of the productions the
// grammar gives a declaration form. The cases check that each factory builds
// that nesting in the order the declarations are written, that no declaration
// is the body and one is the §F.3.2 form, and that under §F.5.5 and §F.5.6.1
// the nested form scopes out every name it declares where a single
// declaration scopes out one.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const SequenceExpr> Atom(const std::string& name) {
  return SeqBoolean(BoolAtom(name));
}

std::shared_ptr<const SequenceExpr> Samp(const std::string& name) {
  return SeqLocalVarSampling(name);
}

const std::vector<LocalVarDeclaration> kVThenW{{"int", "v"}, {"bit", "w"}};

// (int v; bit w; R) is the declaration of v over the declaration of w over R,
// and not the declaration of w over the declaration of v.
TEST(DerivedLocalVariableDeclarations, TheSequenceFormNestsInTheOrderWritten) {
  auto rest = SeqConcat(Samp("v"), Samp("w"));
  auto form = SeqLocalVarDecls(kVThenW, rest);
  ASSERT_EQ(form->kind, SequenceExpr::Kind::kLocalVarDecl);
  EXPECT_EQ(form->local_var_type, "int");
  EXPECT_EQ(form->local_var_name, "v");
  ASSERT_NE(form->lhs, nullptr);
  ASSERT_EQ(form->lhs->kind, SequenceExpr::Kind::kLocalVarDecl);
  EXPECT_EQ(form->lhs->local_var_type, "bit");
  EXPECT_EQ(form->lhs->local_var_name, "w");
  EXPECT_EQ(form->lhs->lhs, rest);
  EXPECT_TRUE(SequenceExprEqual(
      *form, *SeqLocalVarDecl("int", "v", SeqLocalVarDecl("bit", "w", rest))));
  EXPECT_FALSE(SequenceExprEqual(
      *form, *SeqLocalVarDecl("bit", "w", SeqLocalVarDecl("int", "v", rest))));
}

// Three declarations nest three deep, the last written innermost.
TEST(DerivedLocalVariableDeclarations, ThreeDeclarationsNestThreeDeep) {
  auto rest = Atom("a");
  auto form =
      SeqLocalVarDecls({{"int", "v"}, {"bit", "w"}, {"logic", "u"}}, rest);
  EXPECT_TRUE(SequenceExprEqual(
      *form,
      *SeqLocalVarDecl(
          "int", "v",
          SeqLocalVarDecl("bit", "w", SeqLocalVarDecl("logic", "u", rest)))));
}

// No declaration is the body itself, and one declaration is the §F.3.2 form
// with nothing nested inside it.
TEST(DerivedLocalVariableDeclarations, NoneIsTheBodyAndOneIsThePrimitive) {
  auto rest = Atom("a");
  EXPECT_EQ(SeqLocalVarDecls({}, rest), rest);
  auto one = SeqLocalVarDecls({{"int", "v"}}, rest);
  EXPECT_TRUE(SequenceExprEqual(*one, *SeqLocalVarDecl("int", "v", rest)));
  EXPECT_EQ(one->lhs, rest);

  auto body = LvStrong(rest);
  EXPECT_EQ(LvLocalVarDecls({}, body), body);
  auto one_property = LvLocalVarDecls({{"int", "v"}}, body);
  ASSERT_EQ(one_property->kind, LvProperty::Kind::kLocalVarDecl);
  EXPECT_EQ(one_property->local_var_name, "v");
  EXPECT_EQ(one_property->lhs, body);

  auto top = LvTopProperty(body);
  EXPECT_EQ(LvTopLocalVarDecls({}, top), top);
  auto one_top = LvTopLocalVarDecls({{"int", "v"}}, top);
  ASSERT_EQ(one_top->kind, LvTopLevelProperty::Kind::kLocalVarDecl);
  EXPECT_EQ(one_top->local_var_name, "v");
  EXPECT_EQ(one_top->inner, top);
}

// The property form (int v; bit w; P) nests the same way over P, and the
// top-level form over T.
TEST(DerivedLocalVariableDeclarations, ThePropertyFormsNestTheSameWay) {
  auto body = LvStrong(Samp("w"));
  auto form = LvLocalVarDecls(kVThenW, body);
  ASSERT_EQ(form->kind, LvProperty::Kind::kLocalVarDecl);
  EXPECT_EQ(form->local_var_type, "int");
  EXPECT_EQ(form->local_var_name, "v");
  ASSERT_NE(form->lhs, nullptr);
  ASSERT_EQ(form->lhs->kind, LvProperty::Kind::kLocalVarDecl);
  EXPECT_EQ(form->lhs->local_var_type, "bit");
  EXPECT_EQ(form->lhs->local_var_name, "w");
  EXPECT_EQ(form->lhs->lhs, body);

  auto top = LvTopProperty(body);
  auto top_form = LvTopLocalVarDecls(kVThenW, top);
  ASSERT_EQ(top_form->kind, LvTopLevelProperty::Kind::kLocalVarDecl);
  EXPECT_EQ(top_form->local_var_type, "int");
  EXPECT_EQ(top_form->local_var_name, "v");
  ASSERT_NE(top_form->inner, nullptr);
  ASSERT_EQ(top_form->inner->kind, LvTopLevelProperty::Kind::kLocalVarDecl);
  EXPECT_EQ(top_form->inner->local_var_type, "bit");
  EXPECT_EQ(top_form->inner->local_var_name, "w");
  EXPECT_EQ(top_form->inner->inner, top);
}

// Under §F.5.5, (int v; bit w; (1, v = e) ##1 (1, w = e)) hides both names
// from the body and restores the outer binding of each afterwards: from a
// context binding v and u the output binds v to its outer value and u alone,
// where the declaration of v alone lets the sampled w out, and no declaration
// lets both sampled values out.
TEST(DerivedLocalVariableDeclarations, EveryDeclaredNameIsScopedOut) {
  auto body = SeqConcat(Samp("v"), Samp("w"));
  const Word kWord{A({"x"}), A({"y"})};
  const LocalContext kInput{{"v", A({"old"})}, {"u", A({"z"})}};

  auto both =
      TightSatisfactionOutputs(kWord, *SeqLocalVarDecls(kVThenW, body), kInput);
  ASSERT_EQ(both.size(), 1U);
  EXPECT_TRUE(LocalContextEqual(both[0], kInput));

  auto v_alone = TightSatisfactionOutputs(
      kWord, *SeqLocalVarDecls({{"int", "v"}}, body), kInput);
  ASSERT_EQ(v_alone.size(), 1U);
  EXPECT_TRUE(LocalContextEqual(
      v_alone[0],
      LocalContext{{"v", A({"old"})}, {"u", A({"z"})}, {"w", A({"y"})}}));

  auto none =
      TightSatisfactionOutputs(kWord, *SeqLocalVarDecls({}, body), kInput);
  ASSERT_EQ(none.size(), 1U);
  EXPECT_TRUE(LocalContextEqual(
      none[0],
      LocalContext{{"v", A({"x"})}, {"u", A({"z"})}, {"w", A({"y"})}}));
}

// Under §F.5.6.1, the body's verdict passes through every declaration, with
// each declared name hidden from the body: (int v; bit w; strong((1, w = e)))
// holds on one letter from the empty context and from one binding both names,
// and (int v; bit w; strong(a)) fails on a letter without a. The top-level
// form passes and fails the same way.
TEST(DerivedLocalVariableDeclarations, TheBodyVerdictPassesThroughTheNesting) {
  auto holds = LvLocalVarDecls(kVThenW, LvStrong(Samp("w")));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"x"})}, *holds, LocalContext{}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      Word{A({"x"})}, *holds,
      LocalContext{{"v", A({"old"})}, {"w", A({"old"})}}));
  auto fails = LvLocalVarDecls(kVThenW, LvStrong(Atom("a")));
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"b"})}, *fails, LocalContext{}));

  auto top_holds =
      LvTopLocalVarDecls(kVThenW, LvTopProperty(LvStrong(Samp("w"))));
  EXPECT_TRUE(
      PassesTopLevelWithLocals(Word{A({"x"})}, *top_holds, LocalContext{}));
  auto top_fails =
      LvTopLocalVarDecls(kVThenW, LvTopProperty(LvStrong(Atom("a"))));
  EXPECT_TRUE(
      FailsTopLevelWithLocals(Word{A({"b"})}, *top_fails, LocalContext{}));
}

}  // namespace
