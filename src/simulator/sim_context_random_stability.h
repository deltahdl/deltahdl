#pragma once

// The randomization operations SimContext performs on a generator it does not
// hold: §18.14.3 object stability gives every class object its own mt19937 and
// §18.14.2 thread stability gives every process one, so ObjectRng,
// SeedObjectRng and the §18.13.4/§18.13.5 get_randstate/set_randstate pair
// read and write the stream on the ClassObject or the Process handed in and
// touch nothing SimContext stores. The generators kept here are the §18.14.1
// initialization RNGs, one per module, interface or program instance, each
// seeded with the default seed and drawn from to seed the instance's static
// processes and the objects its static declaration initializers create; and
// the seed of $random, which is no generator at all: Table N.1 computes
// $random with the §N.2 rtl_dist_uniform, whose whole state is the 32-bit seed
// it advances.
//
// The default seed is the seed argument of SimContext's constructor and stays
// with the rest of the context in src/simulator/sim_context.h, and so do
// ActiveRng, DrawSeedForChild, Urandom32, SeedUrandom and UrandomRange, each
// of which chooses between the initialization RNG of the instance being built
// and the running process's stream. $random draws from none of them.

#include <cstdint>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>

#include "simulator/class_object.h"
#include "simulator/sim_context_types.h"

namespace delta {

class RandomStability {
 public:
  // §18.14.3 object stability: hand back the generator that belongs solely to
  // this instance. Because every object draws from its own stream, the
  // randomization of one instance is independent of any other instance and of
  // the $random/$urandom and per-thread generators. The stream is materialized
  // lazily from the seed installed at allocation (§18.14.1), so the draw
  // sequence stays reproducible.
  std::mt19937& ObjectRng(ClassObject* obj);

  // §18.14.3: an instance can be reseeded at any time via srandom(), letting an
  // object self-seed (typically inside its new method) so its randomization
  // replays under the chosen seed.
  void SeedObjectRng(ClassObject* obj, uint32_t seed);

  // §18.13.4 get_randstate(): hand back the object's current RNG internal state
  // as a string. mt19937 fully serializes its state through operator<<, so the
  // returned value captures the complete generator state -- not merely the
  // seed -- and reading it does not advance the stream. The string's length and
  // contents are implementation dependent.
  std::string GetRandState(ClassObject* obj);

  // §18.13.4 get_randstate(): the same retrieval for the RNG owned by a process
  // (the state obtained via the process's get_randstate() method).
  std::string GetRandState(Process* proc);

  // §18.13.5 set_randstate(): install `state` as the object's RNG internal
  // state, the inverse of GetRandState. mt19937 round-trips its full state
  // through operator>>, so a value previously produced by GetRandState restores
  // the generator to the exact stream position it was read from. The stream is
  // marked live so a later draw does not reseed over the restored state. The
  // value is treated as an opaque string of implementation-dependent length and
  // format; supplying one not obtained from GetRandState is undefined.
  void SetRandState(ClassObject* obj, const std::string& state);

  // §18.13.5 set_randstate(): the same install for the RNG owned by a process
  // (the state given to the process's set_randstate() method).
  void SetRandState(Process* proc, const std::string& state);

  // §20.14.1 with Table N.1: the seed of the $random stream, the 32-bit state
  // rtl_dist_uniform advances. A call with a seed argument sets it and a call
  // without one continues from it, so the stream the last seed selected is the
  // one the seedless form draws from.
  int32_t* RandomSeed() { return &random_seed_; }

  // §18.14.1: each module, interface and program instance has an
  // initialization RNG seeded with the default seed, from which its static
  // processes and the objects its static declaration initializers create take
  // their seeds. Hands back the one of the instance `prefix` names -- the
  // top's prefix is empty -- creating it seeded with `default_seed` the first
  // time the instance is named, so every instance starts from the same seed
  // and the same static process of two instances of one module draws alike.
  std::mt19937& InitializationRng(std::string_view prefix,
                                  uint32_t default_seed);

 private:
  int32_t random_seed_ = 0;
  std::unordered_map<std::string, std::mt19937> init_rngs_;
};

}  // namespace delta
