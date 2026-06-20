#pragma once

#include "synthesizer/aig.h"

namespace delta {

void ConstProp(AigGraph& g);

void Balance(AigGraph& g);

void Rewrite(AigGraph& g);

void Refactor(AigGraph& g);

void RemoveRedundancy(AigGraph& g);

}  // namespace delta
