#include "elaborator/annex_f_satisfaction_without_local_variables.h"

#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_property_rewrite.h"

namespace delta {

bool SequenceInvolvesLocalVariables(const SequenceExpr& sequence) {
  // §F.3.2: the two local variable forms of R; every other form only carries
  // operands that may hold one.
  switch (sequence.kind) {
    case SequenceExpr::Kind::kLocalVarDecl:
    case SequenceExpr::Kind::kLocalVarSampling:
      return true;
    case SequenceExpr::Kind::kBoolean:
    case SequenceExpr::Kind::kParen:
    case SequenceExpr::Kind::kConcat:
    case SequenceExpr::Kind::kFusion:
    case SequenceExpr::Kind::kOr:
    case SequenceExpr::Kind::kIntersect:
    case SequenceExpr::Kind::kFirstMatch:
    case SequenceExpr::Kind::kNullRepeat:
    case SequenceExpr::Kind::kUnboundedRepeat:
    case SequenceExpr::Kind::kClock:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
      break;
  }
  return (sequence.lhs && SequenceInvolvesLocalVariables(*sequence.lhs)) ||
         (sequence.rhs && SequenceInvolvesLocalVariables(*sequence.rhs));
}

bool PropertyInvolvesLocalVariables(const PropertyExpr& property) {
  // §F.3.2 P: no form of its own declares or samples a local variable, so the
  // question passes to the sequence operand and the sub-properties.
  return (property.sequence &&
          SequenceInvolvesLocalVariables(*property.sequence)) ||
         (property.lhs && PropertyInvolvesLocalVariables(*property.lhs)) ||
         (property.rhs && PropertyInvolvesLocalVariables(*property.rhs));
}

bool TopLevelPropertyInvolvesLocalVariables(const TopLevelProperty& top) {
  return (top.property && PropertyInvolvesLocalVariables(*top.property)) ||
         (top.inner && TopLevelPropertyInvolvesLocalVariables(*top.inner));
}

bool ClockedPropertyInvolvesLocalVariables(const ClockedProperty& property) {
  // §F.3.2 Q: as for P, only the sequence operands can hold one.
  return (property.sequence &&
          SequenceInvolvesLocalVariables(*property.sequence)) ||
         (property.lhs &&
          ClockedPropertyInvolvesLocalVariables(*property.lhs)) ||
         (property.rhs && ClockedPropertyInvolvesLocalVariables(*property.rhs));
}

bool ClockedTopLevelPropertyInvolvesLocalVariables(
    const ClockedTopLevelProperty& top) {
  return (top.property &&
          ClockedPropertyInvolvesLocalVariables(*top.property)) ||
         (top.inner &&
          ClockedTopLevelPropertyInvolvesLocalVariables(*top.inner));
}

bool AssertionInvolvesLocalVariables(const AssertionStatement& assertion) {
  // §F.3.2 A: the clock c is a Boolean and holds no local variable, so only
  // the top-level body can.
  switch (assertion.form) {
    case AssertionStatement::Form::kExplicitClock:
      return assertion.top &&
             TopLevelPropertyInvolvesLocalVariables(*assertion.top);
    case AssertionStatement::Form::kClockedTop:
      return assertion.clocked_top &&
             ClockedTopLevelPropertyInvolvesLocalVariables(
                 *assertion.clocked_top);
  }
  return false;
}

namespace {

LvProperty::Kind LvKindOf(PropertyExpr::Kind kind) {
  // The §F.5.6.1 model repeats the §F.5.3.1 forms one for one and adds the
  // declaration, which no §F.5.3 property has.
  switch (kind) {
    case PropertyExpr::Kind::kStrong:
      return LvProperty::Kind::kStrong;
    case PropertyExpr::Kind::kWeak:
      return LvProperty::Kind::kWeak;
    case PropertyExpr::Kind::kParen:
      return LvProperty::Kind::kParen;
    case PropertyExpr::Kind::kNot:
      return LvProperty::Kind::kNot;
    case PropertyExpr::Kind::kImplication:
      return LvProperty::Kind::kImplication;
    case PropertyExpr::Kind::kOr:
      return LvProperty::Kind::kOr;
    case PropertyExpr::Kind::kAnd:
      return LvProperty::Kind::kAnd;
    case PropertyExpr::Kind::kNexttime:
      return LvProperty::Kind::kNexttime;
    case PropertyExpr::Kind::kUntil:
      return LvProperty::Kind::kUntil;
    case PropertyExpr::Kind::kAcceptOn:
      return LvProperty::Kind::kAcceptOn;
  }
  return LvProperty::Kind::kStrong;
}

LvTopLevelProperty::Kind LvTopKindOf(TopLevelProperty::Kind kind) {
  switch (kind) {
    case TopLevelProperty::Kind::kProperty:
      return LvTopLevelProperty::Kind::kProperty;
    case TopLevelProperty::Kind::kDisableIff:
      return LvTopLevelProperty::Kind::kDisableIff;
    case TopLevelProperty::Kind::kParen:
      return LvTopLevelProperty::Kind::kParen;
  }
  return LvTopLevelProperty::Kind::kProperty;
}

}  // namespace

std::shared_ptr<const LvProperty> AsPropertyWithLocalVariables(
    const PropertyExpr& property) {
  auto lv = std::make_shared<LvProperty>();
  lv->kind = LvKindOf(property.kind);
  lv->sequence = property.sequence;
  lv->boolean = property.boolean;
  if (property.lhs) lv->lhs = AsPropertyWithLocalVariables(*property.lhs);
  if (property.rhs) lv->rhs = AsPropertyWithLocalVariables(*property.rhs);
  return lv;
}

std::shared_ptr<const LvTopLevelProperty> AsTopLevelPropertyWithLocalVariables(
    const TopLevelProperty& top) {
  auto lv = std::make_shared<LvTopLevelProperty>();
  lv->kind = LvTopKindOf(top.kind);
  lv->disable_condition = top.disable_condition;
  if (top.property) lv->property = AsPropertyWithLocalVariables(*top.property);
  if (top.inner) lv->inner = AsTopLevelPropertyWithLocalVariables(*top.inner);
  return lv;
}

}  // namespace delta
