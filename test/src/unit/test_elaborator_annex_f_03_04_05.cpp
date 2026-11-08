#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const SequenceExpr> Atom(const std::string& name) {
  return SeqBoolean(BoolAtom(name));
}

std::shared_ptr<const SequenceExpr> Samp(const std::string& name) {
  return SeqLocalVarSampling(name);
}

std::vector<LocalVarDeclaration> VThenW() {
  return {{"int", "v"}, {"bit", "w"}};
}

TEST(DerivedLocalVariableDeclarations, TheSequenceFormNestsInTheOrderWritten) {
  auto rest = SeqConcat(Samp("v"), Samp("w"));
  auto form = SeqLocalVarDecls(VThenW(), rest);
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

TEST(DerivedLocalVariableDeclarations, ThePropertyFormsNestTheSameWay) {
  auto body = LvStrong(Samp("w"));
  auto form = LvLocalVarDecls(VThenW(), body);
  ASSERT_EQ(form->kind, LvProperty::Kind::kLocalVarDecl);
  EXPECT_EQ(form->local_var_type, "int");
  EXPECT_EQ(form->local_var_name, "v");
  ASSERT_NE(form->lhs, nullptr);
  ASSERT_EQ(form->lhs->kind, LvProperty::Kind::kLocalVarDecl);
  EXPECT_EQ(form->lhs->local_var_type, "bit");
  EXPECT_EQ(form->lhs->local_var_name, "w");
  EXPECT_EQ(form->lhs->lhs, body);

  auto top = LvTopProperty(body);
  auto top_form = LvTopLocalVarDecls(VThenW(), top);
  ASSERT_EQ(top_form->kind, LvTopLevelProperty::Kind::kLocalVarDecl);
  EXPECT_EQ(top_form->local_var_type, "int");
  EXPECT_EQ(top_form->local_var_name, "v");
  ASSERT_NE(top_form->inner, nullptr);
  ASSERT_EQ(top_form->inner->kind, LvTopLevelProperty::Kind::kLocalVarDecl);
  EXPECT_EQ(top_form->inner->local_var_type, "bit");
  EXPECT_EQ(top_form->inner->local_var_name, "w");
  EXPECT_EQ(top_form->inner->inner, top);
}

TEST(DerivedLocalVariableDeclarations, EveryDeclaredNameIsScopedOut) {
  auto body = SeqConcat(Samp("v"), Samp("w"));
  const Word kWord{A({"x"}), A({"y"})};
  const LocalContext kInput{{"v", A({"old"})}, {"u", A({"z"})}};

  auto both = TightSatisfactionOutputs(kWord, *SeqLocalVarDecls(VThenW(), body),
                                       kInput);
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

TEST(DerivedLocalVariableDeclarations, TheBodyVerdictPassesThroughTheNesting) {
  auto holds = LvLocalVarDecls(VThenW(), LvStrong(Samp("w")));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"x"})}, *holds, LocalContext{}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      Word{A({"x"})}, *holds,
      LocalContext{{"v", A({"old"})}, {"w", A({"old"})}}));
  auto fails = LvLocalVarDecls(VThenW(), LvStrong(Atom("a")));
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"b"})}, *fails, LocalContext{}));

  auto top_holds =
      LvTopLocalVarDecls(VThenW(), LvTopProperty(LvStrong(Samp("w"))));
  EXPECT_TRUE(
      PassesTopLevelWithLocals(Word{A({"x"})}, *top_holds, LocalContext{}));
  auto top_fails =
      LvTopLocalVarDecls(VThenW(), LvTopProperty(LvStrong(Atom("a"))));
  EXPECT_TRUE(
      FailsTopLevelWithLocals(Word{A({"b"})}, *top_fails, LocalContext{}));
}

}  // namespace
