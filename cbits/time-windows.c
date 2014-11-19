/*
 * Windows has the most amazingly cretinous time measurement APIs you
 * can possibly imagine.
 *
 * Our first possibility is GetSystemTimeAsFileTime, which updates at
 * roughly 60Hz, and is hence worthless - we'd have to run a
 * computation for tens or hundreds of seconds to get a trustworthy
 * number.
 *
 * Alternatively, we can use QueryPerformanceCounter, which has
 * undefined behaviour under almost all interesting circumstances
 * (e.g. multicore systems, CPU frequency changes). But at least it
 * increments reasonably often.
 */

#include <windows.h>

#if 0

void criterion_inittime(void)
{
}

double criterion_gettime(void)
{
    FILETIME ft;
    ULARGE_INTEGER li;

    GetSystemTimeAsFileTime(&ft);
    li.LowPart = ft.dwLowDateTime;
    li.HighPart = ft.dwHighDateTime;

    return (li.QuadPart - 130000000000000000ull) * 1e-7;
}

#else

static double freq_recip;
static LARGE_INTEGER firstClock;

void criterion_inittime(void)
{
    LARGE_INTEGER freq;

    if (freq_recip == 0) {
	QueryPerformanceFrequency(&freq);
	QueryPerformanceCounter(&firstClock);
	freq_recip = 1.0 / freq.QuadPart;
    }
}

double criterion_gettime(void)
{
    LARGE_INTEGER li;

    QueryPerformanceCounter(&li);

    return ((double) (li.QuadPart - firstClock.QuadPart)) * freq_recip;
}

#endif

static ULONGLONG to_quad_100ns(FILETIME ft)
{
    ULARGE_INTEGER li;
    li.LowPart = ft.dwLowDateTime;
    li.HighPart = ft.dwHighDateTime;
    return li.QuadPart;
}

double criterion_getcputime(void)
{
    FILETIME creation, exit, kernel, user;
    ULONGLONG time;

    GetProcessTimes(GetCurrentProcess(), &creation, &exit, &kernel, &user);

    time = to_quad_100ns(user) + to_quad_100ns(kernel);
    return time / 1e7;
}
