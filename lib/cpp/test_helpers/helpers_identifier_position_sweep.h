#pragma once

#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_keyword_version.h"
#include "model_identifier_positions.h"

using namespace delta;

// Sweeps over the identifier positions of model_identifier_positions.h, for a
// test whose subject is what a `begin_keywords version_specifier reserves.
// Both sweeps take the positions to cover as a list of names; an empty list
// covers every position.

// Every word of `words` put into each covered position and rejected under
// `spec`. A word the specifier reserves cannot name anything, so no position
// admits it.
inline void ExpectWordsFillNoIdentifierPosition(
    const char* spec, std::initializer_list<const char*> words,
    std::initializer_list<std::string_view> positions = {}) {
  for (const auto& p : kIdentifierPositions) {
    if (positions.size() != 0 && !PositionIsOneOf(p, positions)) continue;
    for (const char* word : words) {
      EXPECT_FALSE(ParseWithPreprocessorOk(In(spec, AtPosition(p, word))))
          << word << " cannot name a " << p.what << " under this version";
    }
  }
}

// The accepting counterpart, which is what keeps the rejections above from
// being blamed on the positions themselves: the same sources under `earlier`,
// a specifier whose list leaves these words free, are accepted. Pairing the
// two legs per position is the whole claim -- the word is reserved *here* and
// an ordinary identifier *there*.
inline void ExpectWordsNameEntitiesUnder(
    const char* earlier, const char* spec,
    std::initializer_list<const char*> words,
    std::initializer_list<std::string_view> positions = {}) {
  for (const auto& p : kIdentifierPositions) {
    if (positions.size() != 0 && !PositionIsOneOf(p, positions)) continue;
    for (const char* word : words) {
      std::string src = AtPosition(p, word);
      EXPECT_TRUE(ParseWithPreprocessorOk(In(earlier, src)))
          << p.what << ": everything this version includes leaves " << word
          << " free";
      EXPECT_FALSE(ParseWithPreprocessorOk(In(spec, src)))
          << p.what << ": this version reserves " << word;
    }
  }
}
