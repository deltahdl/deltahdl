#pragma once

#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

using namespace delta;

using NameSet = std::set<std::string>;

inline Letter A(std::set<std::string> atoms) {
  return LetterAtoms(std::move(atoms));
}

inline auto Bool(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

inline auto Samp(const std::string& name) { return SeqLocalVarSampling(name); }

inline bool SameContexts(const std::vector<LocalContext>& lhs,
                         const std::vector<LocalContext>& rhs) {
  if (lhs.size() != rhs.size()) {
    return false;
  }
  for (const LocalContext& a : lhs) {
    bool found = false;
    for (const LocalContext& b : rhs) {
      if (LocalContextEqual(a, b)) {
        found = true;
        break;
      }
    }
    if (!found) {
      return false;
    }
  }
  return true;
}
