#include <sys/resource.h>
#include <sys/time.h>

#include <chrono>
#include <iostream>
#include <tuple>
#include <unordered_map>

namespace {

// https://stackoverflow.com/a/6245777/1937836
namespace aux {
template <std::size_t...>
struct seq {};

template <std::size_t N, std::size_t... Is>
struct gen_seq : gen_seq<N - 1, N - 1, Is...> {};

template <std::size_t... Is>
struct gen_seq<0, Is...> : seq<Is...> {};

template <class Ch, class Tr, class Tuple, std::size_t... Is>
void print_tuple(std::basic_ostream<Ch, Tr>& os, Tuple const& t, seq<Is...>) {
  using swallow = int[];
  (void)swallow{0,
                (void(os << (Is == 0 ? "" : ", ") << std::get<Is>(t)), 0)...};
}
}  // namespace aux

template <class Ch, class Tr, class... Args>
auto operator<<(std::basic_ostream<Ch, Tr>& os, std::tuple<Args...> const& t)
    -> std::basic_ostream<Ch, Tr>& {
  aux::print_tuple(os, t, aux::gen_seq<sizeof...(Args)>());
  return os;
}

template <typename T, typename U, typename Hash, typename Pred>
std::ostream& operator<<(std::ostream& os,
                         const std::unordered_map<T, U, Hash, Pred>& m) {
  for (auto&& p : m) {
    os << p.first << ": " << p.second << '\n';
  }
  return os;
}

template <typename F>
void time(F f, char const* tag, int reps) {
  using fsec = std::chrono::duration<double>;
  using usec = std::chrono::microseconds;
  using std::chrono::steady_clock;
  using std::chrono::system_clock;

  auto as_fsec = [](auto dur) { return std::chrono::duration_cast<fsec>(dur); };
  auto tv_diff = [](timeval start, timeval end) {
    auto start_sec = system_clock::from_time_t(start.tv_sec);
    auto end_sec = system_clock::from_time_t(end.tv_sec);
    return std::chrono::duration_cast<usec>(end_sec - start_sec) +
           (usec(end.tv_usec) - usec(start.tv_usec));
  };

  steady_clock::duration total_real{0};
  usec total_user{0};
  usec total_sys{0};

  for (int i = 0; i < reps; i++) {
    struct rusage s_start;
    getrusage(RUSAGE_SELF, &s_start);
    auto rep_start = steady_clock::now();

    auto val = f();

    auto rep_end = steady_clock::now();
    struct rusage s_end;
    getrusage(RUSAGE_SELF, &s_end);

    auto udiff = tv_diff(s_start.ru_utime, s_end.ru_utime);
    auto sdiff = tv_diff(s_start.ru_stime, s_end.ru_stime);
    std::cout << tag << " val: " << std::fixed << val << std::endl;
    std::cout << tag << " took (s): real " << as_fsec(rep_end - rep_start)
              << " user " << as_fsec(udiff) << " sys " << as_fsec(sdiff)
              << std::endl;

    total_real += rep_end - rep_start;
    total_user += udiff;
    total_sys += sdiff;
  }

  std::cout << tag << " took (avg): real " << (as_fsec(total_real) / reps)
            << " user " << (as_fsec(total_user) / reps) << " sys "
            << (as_fsec(total_sys) / reps) << std::endl;
}

namespace hash_tuple {

template <typename TT>
struct hash {
  size_t operator()(TT const& tt) const { return std::hash<TT>()(tt); }
};

namespace {
template <class T>
inline void hash_combine(std::size_t& seed, T const& v) {
  seed ^= hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

template <class Tuple, size_t Index = std::tuple_size<Tuple>::value - 1>
struct HashValueImpl {
  static void apply(size_t& seed, Tuple const& tuple) {
    HashValueImpl<Tuple, Index - 1>::apply(seed, tuple);
    hash_combine(seed, std::get<Index>(tuple));
  }
};

template <class Tuple>
struct HashValueImpl<Tuple, 0> {
  static void apply(size_t& seed, Tuple const& tuple) {
    hash_combine(seed, std::get<0>(tuple));
  }
};
}  // namespace

template <typename... TT>
struct hash<std::tuple<TT...>> {
  size_t operator()(std::tuple<TT...> const& tt) const {
    size_t seed = 0;
    HashValueImpl<std::tuple<TT...>>::apply(seed, tt);
    return seed;
  }
};

}  // namespace hash_tuple

}  // namespace
