#pragma once

#include <memory>

#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"

namespace delta {

bool LvPropertyInvolvesLocalVariables(const LvProperty& property);
bool LvTopLevelPropertyInvolvesLocalVariables(const LvTopLevelProperty& top);

std::shared_ptr<const PropertyExpr> AsPropertyWithoutLocalVariables(
    const LvProperty& property);
std::shared_ptr<const TopLevelProperty> AsTopLevelPropertyWithoutLocalVariables(
    const LvTopLevelProperty& top);

}  // namespace delta
