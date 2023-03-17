#include <sys/resource.h>
#include <sys/time.h>

#include <chrono>
#include <iostream>
#include <unordered_map>

namespace {

template <typename T, typename U>
std::ostream& operator<<(std::ostream& os, const std::unordered_map<T, U>& m) {
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

}
