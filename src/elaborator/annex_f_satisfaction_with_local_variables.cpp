#include "elaborator/annex_f_satisfaction_with_local_variables.h"

#include <memory>
#include <optional>

#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_satisfaction_without_local_variables.h"

namespace delta {

bool LvPropertyInvolvesLocalVariables(const LvProperty& property) {
  // §F.5.6: the declaration form is the property's own; the sequence operand
  // may carry the forms of §F.3.2; the sub-properties are searched in turn.
  if (property.kind == LvProperty::Kind::kLocalVarDecl) {
    return true;
  }
  if (property.sequence && SequenceInvolvesLocalVariables(*property.sequence)) {
    return true;
  }
  return (property.lhs && LvPropertyInvolvesLocalVariables(*property.lhs)) ||
         (property.rhs && LvPropertyInvolvesLocalVariables(*property.rhs));
}

bool LvTopLevelPropertyInvolvesLocalVariables(const LvTopLevelProperty& top) {
  if (top.kind == LvTopLevelProperty::Kind::kLocalVarDecl) {
    return true;
  }
  return (top.property && LvPropertyInvolvesLocalVariables(*top.property)) ||
         (top.inner && LvTopLevelPropertyInvolvesLocalVariables(*top.inner));
}

namespace {

// The §F.5.3.1 form a §F.5.6.1 form retracts to, or none for the declaration,
// which no §F.5.3 property has.
std::optional<PropertyExpr::Kind> KindOf(LvProperty::Kind kind) {
  switch (kind) {
    case LvProperty::Kind::kStrong:
      return PropertyExpr::Kind::kStrong;
    case LvProperty::Kind::kWeak:
      return PropertyExpr::Kind::kWeak;
    case LvProperty::Kind::kParen:
      return PropertyExpr::Kind::kParen;
    case LvProperty::Kind::kNot:
      return PropertyExpr::Kind::kNot;
    case LvProperty::Kind::kImplication:
      return PropertyExpr::Kind::kImplication;
    case LvProperty::Kind::kOr:
      return PropertyExpr::Kind::kOr;
    case LvProperty::Kind::kAnd:
      return PropertyExpr::Kind::kAnd;
    case LvProperty::Kind::kNexttime:
      return PropertyExpr::Kind::kNexttime;
    case LvProperty::Kind::kUntil:
      return PropertyExpr::Kind::kUntil;
    case LvProperty::Kind::kAcceptOn:
      return PropertyExpr::Kind::kAcceptOn;
    case LvProperty::Kind::kLocalVarDecl:
      return std::nullopt;
  }
  return std::nullopt;
}

std::optional<TopLevelProperty::Kind> TopKindOf(LvTopLevelProperty::Kind kind) {
  switch (kind) {
    case LvTopLevelProperty::Kind::kProperty:
      return TopLevelProperty::Kind::kProperty;
    case LvTopLevelProperty::Kind::kDisableIff:
      return TopLevelProperty::Kind::kDisableIff;
    case LvTopLevelProperty::Kind::kParen:
      return TopLevelProperty::Kind::kParen;
    case LvTopLevelProperty::Kind::kLocalVarDecl:
      return std::nullopt;
  }
  return std::nullopt;
}

}  // namespace

std::shared_ptr<const PropertyExpr> AsPropertyWithoutLocalVariables(
    const LvProperty& property) {
  // §F.5.6: outside the fragment without local variables there is nothing to
  // retract to; inside it, the shape is kept operator for operator.
  const std::optional<PropertyExpr::Kind> kKind = KindOf(property.kind);
  if (!kKind || LvPropertyInvolvesLocalVariables(property)) {
    return nullptr;
  }
  auto p = std::make_shared<PropertyExpr>();
  p->kind = *kKind;
  p->sequence = property.sequence;
  p->boolean = property.boolean;
  if (property.lhs) p->lhs = AsPropertyWithoutLocalVariables(*property.lhs);
  if (property.rhs) p->rhs = AsPropertyWithoutLocalVariables(*property.rhs);
  return p;
}

std::shared_ptr<const TopLevelProperty> AsTopLevelPropertyWithoutLocalVariables(
    const LvTopLevelProperty& top) {
  const std::optional<TopLevelProperty::Kind> kKind = TopKindOf(top.kind);
  if (!kKind || LvTopLevelPropertyInvolvesLocalVariables(top)) {
    return nullptr;
  }
  auto t = std::make_shared<TopLevelProperty>();
  t->kind = *kKind;
  t->disable_condition = top.disable_condition;
  if (top.property)
    t->property = AsPropertyWithoutLocalVariables(*top.property);
  if (top.inner) t->inner = AsTopLevelPropertyWithoutLocalVariables(*top.inner);
  return t;
}

}  // namespace delta
