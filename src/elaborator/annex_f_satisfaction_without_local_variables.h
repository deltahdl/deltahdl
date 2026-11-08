#pragma once

#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_property_rewrite.h"

namespace delta {

bool SequenceInvolvesLocalVariables(const SequenceExpr& sequence);

bool PropertyInvolvesLocalVariables(const PropertyExpr& property);
bool TopLevelPropertyInvolvesLocalVariables(const TopLevelProperty& top);
bool ClockedPropertyInvolvesLocalVariables(const ClockedProperty& property);
bool ClockedTopLevelPropertyInvolvesLocalVariables(
    const ClockedTopLevelProperty& top);

bool AssertionInvolvesLocalVariables(const AssertionStatement& assertion);

std::shared_ptr<const LvProperty> AsPropertyWithLocalVariables(
    const PropertyExpr& property);
std::shared_ptr<const LvTopLevelProperty> AsTopLevelPropertyWithLocalVariables(
    const TopLevelProperty& top);

}  // namespace delta
