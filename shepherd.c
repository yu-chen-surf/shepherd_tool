/*
 * shepherd.c
 * Scheduler Helper Daemon
 *
 * see shepherd.1 for details
 *
 * This program is free software, released under GPLv2
 * Copyright (C) 2016 Len Brown, Intel Corp <len.brown@intel.com>
 */

#define _GNU_SOURCE             /* See feature_test_macros(7) */
#include <sched.h>

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <getopt.h>
#include <errno.h>
#include <signal.h>
#include <sched.h>
#include <stddef.h>
#include <string.h>
#include <sys/prctl.h>
#include <time.h>
#include <err.h>
#include <dirent.h>
#include <mntent.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/mount.h>
#include <syslog.h>

#include "cpuset.c"

#define UNUSED(x) unsigned int UNUSED_ ## x __attribute__((__unused__))
#ifndef PATH_MAX
#  ifdef MAXPATHLEN
#    define PATH_MAX MAXPATHLEN
#  else
#    define PATH_MAX 2048
#  endif
#endif

unsigned int debug;
unsigned int max_cpu_num;
unsigned int present_num_cpus;

cpu_set_t *cpuset_present;
cpu_set_t *cpuset_active;
size_t system_cpuset_size;

char *proc_stat = "/proc/stat";
char *proc_loadavg = "/proc/loadavg";

long user_tick_per_sec;
double poll_slow_sec;
double poll_norm_sec;
double poll_fast_sec;

int  exit_main_loop;
FILE *dfp;
char *output_path;
int cgroupv2 = 0;

/*
 * cpuset_size_floor
 * the CPU set will not shrink smaller than cpuset_size_floor
 */
int cpuset_size_floor = 1;

/*
 * cpuset_size_ceiling
 * the CPU set will not grow no larger than cpuset_size_ceiling
 */
int cpuset_size_ceiling;

#define HISTORY_LENGTH 10

struct cpuset_history {
	double seconds;
	unsigned cpuset_num_cpus;
	unsigned long long system_idle_tick_sum;
} history[HISTORY_LENGTH];

unsigned int *set_size_choosen;
double *set_size_seconds;

static void debug_dump_history(void)
{
	int i;

	for (i = 0; i < HISTORY_LENGTH; ++i)
	{
		fprintf(dfp, "history[%d] %d cpus %f sec %lld sum\n",
			i,
			history[i].cpuset_num_cpus,
			history[i].seconds,
			history[i].system_idle_tick_sum);
	}
}
#ifdef NOTYET
/*
 * up_slope_max -- how fast a set can grow per interval
 * 1.00 means it can increase by up to 100% of its current size
 * 0.50 means it can increase by up to 50% of its current size
 * etc.
 */
double up_slope_max = 0.50;
#endif

#ifdef NOTYET
/*
 * up_cpus_max
 * maximum number of CPUs to increase set per interval
 * default = cpuset_size_ceiling/4;
 */
int up_cpus_max;
#endif

#ifdef NOTYET
/*
 * down_rate
 * 0.50 means shrink at 50% of the way to ideal_set size on each interval
 */
double down_rate = 0.5;
#endif


/*
 * get_next_polling_interval_sec()
 *
 * Policy decision:
 * return ns for next polling interval
 */
static double get_next_polling_interval_sec(double average_utilization, int set_size)
{
	
	/*
	 * If max set size, then poll normally,
	 * no matter the utilization.  We can't grow more,
	 * and we are not in a big rush to shrink.
	 */
	if (set_size == cpuset_size_ceiling)
		return poll_norm_sec;

	/*
	 * If min set and very low utilization, poll slowly, 
	 * to minimally disturb profoundly idle system.
	 */
	if ((set_size == cpuset_size_floor) && (average_utilization < 5))
		return poll_slow_sec;

	/*
	 * If high utilzation, poll quickly
	 * to promptly expand capacity with demand
	 */
	if (average_utilization > 80)
		return poll_fast_sec; 

	/*
	 * poll at moderate rate
	 */
	return poll_norm_sec;
}

#ifdef NOTYET
/*
 * Timer slack gives the kernel permission to coalesce our timeout
 * with nearby system timers.  System default is +/- 0.050 ms,
 * which is much tighter than we need.  Increase timer slack
 * to 1/16th of the requested timeout duration, eg.
 *
 *    10 ms / 16 = +/-   0.625 ms
 *   100 ms / 16 = +/-  6.25 ms
 * 1,000 ms / 16 = +/-  62.5 ms
 * 2,000 ms / 16 = +/- 125.0 ms
 */

unsigned int debug_timer_slack_updates;

unsigned long timer_slack_current_ns;
static void timer_slack_check(double sleep_sec)
{
	unsigned long timer_slack_desired_ns;

	timer_slack_desired_ns = (unsigned long long)sleep_sec / 16 * 1000000000;

	if (timer_slack_desired_ns == timer_slack_current_ns)
		return;

	debug_timer_slack_updates++;

	if (prctl(PR_SET_TIMERSLACK, timer_slack_desired_ns) < 0)
		err(-1, "PR_SET_TIMERSLACK");

	timer_slack_current_ns = timer_slack_desired_ns;
}
#endif

static double timestamp_sec(void)
{
	struct timespec ts;

	if (clock_gettime(CLOCK_REALTIME, &ts) < 0)
		err(-1, "clock_gettime");

	return ((double)ts.tv_sec + (double)ts.tv_nsec/1000000000);
}

struct timespec ts_begin, ts_end;

#define DEBUG_SLEEP_ARRAY_SIZE	12	

unsigned int sleep_request_histogram[DEBUG_SLEEP_ARRAY_SIZE];
unsigned int sleep_actual_histogram[DEBUG_SLEEP_ARRAY_SIZE];

unsigned int debug_sleep_count;
double debug_sleep_stats_start_time;

static void debug_sleep_histogram_record(unsigned int *a, double interval)
{
	int i;

	for (i = 0; i < DEBUG_SLEEP_ARRAY_SIZE; ++i) {
		if (interval >= 2.0) {
			a[i]++;
			return;
		}
		interval *= 2;
	}
}
static void debug_sleep_histograms_clear(void)
{
	int i;

	for (i = 0; i < DEBUG_SLEEP_ARRAY_SIZE; ++i) {
		sleep_request_histogram[i] = 0;
		sleep_actual_histogram[i] = 0;
	}

	debug_sleep_stats_start_time = timestamp_sec();
}
static void debug_sleep_histograms_dump(void)
{
	int i;
	double seconds = 2.0;
	unsigned int request_count, actual_count;
	double now, interval;

	request_count = actual_count = 0;

	fprintf(dfp, "Sleep Wake    Seconds\n");
	for (i = 0; i < DEBUG_SLEEP_ARRAY_SIZE; ++i) {
		request_count += sleep_request_histogram[i];
		actual_count += sleep_actual_histogram[i];
		fprintf(dfp, "%5d %4d >= %f\n",
			sleep_request_histogram[i],
			sleep_actual_histogram[i], seconds);
		seconds /= 2;
	}
	now = timestamp_sec();
	interval = now - debug_sleep_stats_start_time;
	fprintf(dfp, "%5d %4d  Total, %f per second over %.2f seconds\n",
		request_count, actual_count,
		(double)request_count/(interval), interval);
}

static void stats_clear(void)
{
	unsigned int cpus;

	for (cpus = 0; cpus <= present_num_cpus; ++cpus) {
		set_size_choosen[cpus] = 0;
		set_size_seconds[cpus] = 0.0;
	}
	debug_sleep_histograms_clear();
}
static void stats_init(void)
{
	set_size_choosen = calloc(present_num_cpus + 1, sizeof(unsigned int));
	if (set_size_choosen == NULL)
		err(1, "calloc(%d, %zd)", present_num_cpus + 1, sizeof(unsigned int));

	set_size_seconds = calloc(present_num_cpus + 1, sizeof(double));
	if (set_size_seconds == NULL)
		err(1, "calloc(%d, %zd)", present_num_cpus + 1, sizeof(double));

	stats_clear();
}

static void stats_dump(void)
{
	unsigned int cpus;

	fprintf(dfp, "CPUs  Used Duration[sec]\n");

	for (cpus = 1; cpus <= present_num_cpus; ++cpus) {
		fprintf(dfp, "%4d  %4d %8.2f\n",
			cpus, set_size_choosen[cpus], set_size_seconds[cpus]);
	}
}

static void dump_statistics(void)
{
	stats_dump();
	debug_sleep_histograms_dump();

#if NOTYET
	fprintf(dfp, "%u%% timer slack updates (%u)\n",
		100 * debug_timer_slack_updates/debug_sleep_count, debug_timer_slack_updates);

	debug_timer_slack_updates = 0;
	debug_sleep_count = 0;
#endif
	stats_clear();
	debug_sleep_histograms_clear();
}

/*
 * sleep_for_sec(sec)
 *
 * Sleep for 'ns' nanosec
 * First allow adjustment to timer_slack
 */

static void sleep_for_sec(double seconds)
{
	struct timespec ts;

	debug_sleep_count++;
	debug_sleep_histogram_record(sleep_request_histogram, seconds);

#if NOTYET
	timer_slack_check(seconds);
#endif

	ts.tv_sec = (time_t)seconds;

	if (debug > 1)
		fprintf(dfp, "input seconds %f -> tv seconds %lld\n",
			seconds, (long long int)ts.tv_sec);

	seconds = seconds - ts.tv_sec;
	ts.tv_nsec = (long)(seconds * 1000000000.0);

	if (debug > 1)
		fprintf(dfp, "input seconds * 1B %f -> tv nsec %ld\n",
			seconds * 1000000000, ts.tv_nsec);

	if (nanosleep(&ts, NULL) < 0) {
		if (errno == EINTR) {
			/* early return if signaled */
			return;
		}
		err(-1, "nanosleep");
	}
}

void copy_file_by_line(char *from_path, char *to_path);
void write_file_value(char *path, char *val);
char *exempt_process;

char cpuset_base[] = "/shepherd";
char cpuset_balloon[] = "balloon";
char cpuset_exempt[] = "exempt";

static void __attribute__((__noreturn__)) usage(FILE *out)
{
	fprintf(out, "shepherd 17.05.21a (C) 2017 Len Brown <len.brown@intel.com>\n");
	fprintf(out, "Usage: shepherd [options]\n");
	fprintf(out, "'man shepherd' for details\n");

	exit(out == stderr ? EXIT_FAILURE: EXIT_SUCCESS);
}

void add_exempt_task(char *pid)
{
	printf("adding pid:%s\n", pid);
	if (cgroupv2) {
		write_file_value("/shepherd/exempt/cgroup.procs", pid);
	} else {
		write_file_value("/shepherd/exempt/tasks", pid);
	}
}

void init_exempt_group(void)
{
	if (cgroupv2) {
		copy_file_by_line("cpuset.mems.effective", "exempt/cpuset.mems");
		copy_file_by_line("cpuset.cpus.effective", "exempt/cpuset.cpus");
	} else {
		copy_file_by_line("cpuset.mems", "exempt/cpuset.mems");
		copy_file_by_line("cpuset.cpus", "exempt/cpuset.cpus");
	}
}

int match_exempt_task(char *name)
{
	/* TBD: >1 tasks */
	return !strcmp(name, exempt_process);
}

/* Borrowed the code from killall5.c */
int add_exempt_tasks(void)
{
	DIR		*dir;
	FILE		*fp;
	struct dirent	*d;
	struct stat	st;
	char		path[PATH_MAX+1];
	char		buf[PATH_MAX+1];
	char		*n1, *n2, *p;
	unsigned long	startcode, endcode;
	int		pid, f;
	ssize_t		len;
        char            process_status[11];

	init_exempt_group();

	/* Open the /proc directory. */
	if (chdir("/proc") == -1)
		err(1, "chdir /proc failed");

	if ((dir = opendir(".")) == NULL)
		err(1, "cannot opendir(/proc)");

	/* Walk through the directory. */
	while ((d = readdir(dir)) != NULL) {

		/* See if this is a process */
		if ((pid = atoi(d->d_name)) == 0)
			continue;

		/* Open the stat file. */
		snprintf(path, sizeof(path), "%s/stat", d->d_name);

		if ((fp = fopen(path, "r")) != NULL) {
			size_t len;

			len = fread(buf, sizeof(char), sizeof(buf)-1, fp);
			buf[len] = '\0';

			if (buf[0] == '\0') {
				fclose(fp);
				continue;
			}

			p = buf;
			n1 = strchr(buf, ' ');
			*n1++ = '\0';
			n1 = strrchr(n1, '(');
			if (n1) {
				/* Read program name. */
				n1++;
				n2 = strchr(n1, ')');
				if (n2 == NULL) {
					fclose(fp);
					continue;
				}
				*n2 = '\0';
			} else {
				continue;
			}
			if (match_exempt_task(n1)) {
				add_exempt_task(p);
			}
			fclose(fp);
		}
	}
	closedir(dir);

	/* Must switch back. */
	if (chdir(cpuset_base))
		err(1, "%s", cpuset_base);
	/* Done. */
	return 0;
}

static void cmdline(int argc, char **argv)
{
	int c;

	static const struct option longopts[] = {
		{ "debug",	0, NULL, 'd' },
		{ "help",	0, NULL, 'h' },
		{ "output",	0, NULL, 'o' },
		{ "cgroupv2",	0, NULL, 'c' },
		{ "exempt",	0, NULL, 'e' },
	};

	while ((c = getopt_long_only(argc, argv, "+dcho:e:", longopts, NULL)) != -1) {
		switch (c) {
		case 'd':
			debug++;
			break;
		case 'h':
			usage(stdout);
			break;
		case 'o':
			output_path = optarg;
			break;
		case 'c':
			cgroupv2 = 1;
			break;
		case 'e':
			exempt_process = optarg;
			break;
		default:
			usage(stderr);
			break;
		}
	}
}

static void init_default_sample_rates(void)
{

	double user_tick_sec;

	user_tick_per_sec = sysconf(_SC_CLK_TCK);

	if (user_tick_per_sec != 100)
		warnx("User ticks %ld, expected 100", user_tick_per_sec);
		
	user_tick_sec = 1.0 / user_tick_per_sec;

	/*
	 * Nominal wakeup frequency is once per second
	 * 1.0 sec/sample = 1 sample/sec
	 */
	poll_norm_sec = 1;

	/*
	 * Slow wakeup frequency is used during profound idle
	 * and at max utilization of full set size
	 * 2.0 sec/sample = 0.5 sample/sec
	 */
	poll_slow_sec = 2;

	/*
	 * Fast wakeup frequency is used at high utilization
	 * Sample at 10 * user user tick rate, which means
	 * we will see at most 10 counter ticks/cpu/sample.
	 * Since user_tick_sec = 10ms,
	 * sample rate = 10 * 10ms = 100ms = 10 samples/sec
	 */
	poll_fast_sec =  user_tick_sec * 10;

}

static void defaults_init(void)
{
	init_default_sample_rates();

	// set_size_ceiling = TBD;

}
/*
 * Open a file, and exit on failure
 */
static FILE *fopen_or_die(const char *path, const char *mode)
{
	FILE *filep = fopen(path, mode);
	if (!filep)
		err(1, "%s: open failed", path);
	return filep;
}
/*
 * run func(cpu) on every cpu in /proc/stat
 * return sum of return values of func(cpu)
 * else, if func() returns negative value, return that.
 */
static unsigned long long sum_for_all_proc_cpus(int (func)(unsigned int, unsigned int, unsigned int, unsigned int, unsigned int, unsigned int), unsigned int arg)
{
	FILE *fp;
	int cpu_num, user, nice, system, idle;
	int retval;
	unsigned long long sum = 0;

	fp = fopen_or_die(proc_stat, "r");

	retval = fscanf(fp, "cpu %*d %*d %*d %*d %*d %*d %*d %*d %*d %*d\n");
	if (retval != 0)
		err(1, "%s: failed to parse format", proc_stat);

	while (1) {
		retval = fscanf(fp, "cpu%u %d %d %d %d %*d %*d %*d %*d %*d %*d\n",
			&cpu_num, &user, &nice, &system, &idle);
		if (retval != 5)
			break;

		retval = func(arg, cpu_num, user, nice, system, idle);
		if (retval < 0) {
			fclose(fp);
			return(retval);
		}
		sum += retval;
	}
	fclose(fp);
	return sum;
}

static unsigned int get_num_runnable_threads(void)
{
	FILE *fp;
	int retval;
	unsigned int num_threads;

	fp = fopen_or_die(proc_loadavg, "r");

	retval = fscanf(fp, "%*f %*f %*f %ud/%*d %*d\n", &num_threads);
	if (retval != 1)
		err(1, "%s", proc_stat);

	if (debug > 2)
		fprintf(dfp, "%d threads\n",  num_threads);
	fclose(fp);

	return num_threads;
}
#if NOTYET
static int for_all_cpuset_cpus(cpu_set_t *set, int (func)(unsigned int))
{
	unsigned int cpu;
	int retval;

	for (cpu = 0; cpu <= max_cpu_num; ++cpu) {
		if (!CPU_ISSET_S(cpu, system_cpuset_size, set))
			continue;
		retval = func(cpu);
		if (retval)
			return retval;
	}
	return 0;
}
#endif
/*
 * cpu_count()
 * update global max_cpu_num, return 1 (per cpu)
 */
static int cpu_count(UNUSED(arg), unsigned int cpu, UNUSED(a), UNUSED(b), UNUSED(c), UNUSED(d))
{
	if (cpu > max_cpu_num)
		max_cpu_num = cpu;

	if (debug > 1)
		fprintf(dfp, "cpu%d: %d\n", cpu, present_num_cpus);
	return 1;
}

static int cpu_mark_present(UNUSED(arg), unsigned int cpu, UNUSED(a), UNUSED(b), UNUSED(c), UNUSED(d))
{
	CPU_SET_S(cpu, system_cpuset_size, cpuset_present);
	return 0;
}

/*
 * for given CPU, starting with INDEX 0
 * Find first /sys/devices/system/cpu/$CPU/cache/$INDEX/shared_cpu_list
 * and return it in cpuset_cache_topology arg
 *
 * return 0 on success, non-0 on failure
 */
static int get_cache_shared_cpu_list(unsigned int cpu_num, cpu_set_t *cpuset_cache_topology)
{
	FILE *fp;
	int index;
	char buf[256];

int retval;

	for (index = 0; index < 10; ++index) {
		char *s;

		sprintf(buf, "/sys/devices/system/cpu/cpu%d/cache/index%d", cpu_num, index);
		if (access(buf, R_OK) != 0) {
			if (debug)
				perror(buf);
			return -1;
		}
		sprintf(buf, "/sys/devices/system/cpu/cpu%d/cache/index%d/shared_cpu_list", cpu_num, index);
		fp = fopen(buf, "r");
		if (fp == NULL) {
			if (debug) perror(buf);
			continue;
		}

		if (fgets(buf, sizeof(buf), fp) == NULL)
			err(1, "%s", buf);

		s = strchr(buf, '\n');
		*s = '\0';

		if (debug > 1)
			fprintf(dfp, "get_cache_shared_cpu_list(%d): read '%s'\n", cpu_num, buf);
		retval = cpulist_parse(buf, cpuset_cache_topology, system_cpuset_size, 1);
		return retval;
	}
	return -1;
}
/*
 * cpus[i] is the order that CPUs are added to the set.
 * This mapping is used to allocate cpus to the set in "topology order".
 * But even for a linear mapping it is needed to deal with sparse numbering.
 */ 
unsigned int *cpus;

static void topology_init_cpu_order(void)
{
	int index;
	unsigned int cpu_num;
	cpu_set_t *cpuset_cache_topology, *cpuset_unprocessed;

	cpuset_cache_topology = CPU_ALLOC((max_cpu_num + 1));
	if (cpuset_cache_topology == NULL)
		err(3, "CPU_ALLOC");

	cpuset_unprocessed = CPU_ALLOC((max_cpu_num + 1));
	if (cpuset_unprocessed == NULL)
		err(3, "CPU_ALLOC");

	CPU_ZERO_S(system_cpuset_size, cpuset_unprocessed);

	CPU_OR_S(system_cpuset_size, cpuset_unprocessed, cpuset_unprocessed, cpuset_active);

	for (index = 0, cpu_num = 0; cpu_num <= max_cpu_num; ++cpu_num) {
		unsigned int cache_cpu_num;

		if (!CPU_ISSET_S(cpu_num, system_cpuset_size, cpuset_unprocessed))
			continue;

		CPU_ZERO_S(system_cpuset_size, cpuset_cache_topology);
		if (get_cache_shared_cpu_list(cpu_num, cpuset_cache_topology)) {
			if (debug) fprintf(dfp, "BAILING to LINEAR\n");
			break;
		}
		for (cache_cpu_num = 0; cache_cpu_num <= max_cpu_num; ++cache_cpu_num)
		{
			if (!CPU_ISSET_S(cache_cpu_num, system_cpuset_size, cpuset_cache_topology))
				continue;
			cpus[index] = cache_cpu_num;
			if (debug)
				fprintf(dfp, "%d: cpus[%d] = cpu%d\n", cpu_num, index, cache_cpu_num);
			CPU_CLR_S(cache_cpu_num, system_cpuset_size, cpuset_unprocessed);
			index++;
		}
	}

	CPU_FREE(cpuset_cache_topology);
	CPU_FREE(cpuset_unprocessed);

	if (cpu_num == max_cpu_num + 1)
		return;

	fprintf(dfp, "BACKUP plan: linear %d\n", cpu_num);
	/* linear */
	for (index = 0, cpu_num = 0; cpu_num <= max_cpu_num; ++cpu_num) {
		if (CPU_ISSET_S(cpu_num, system_cpuset_size, cpuset_active)) {
			cpus[index] = cpu_num;
			if (debug > 1)
				fprintf(dfp, "cpus[%d] = cpu%d\n", index, cpu_num);
			index++;
		}
	}
}

static void topology_probe(void)
{
	present_num_cpus = 0;
	max_cpu_num = 0;
	present_num_cpus = sum_for_all_proc_cpus(cpu_count, 0);
	cpuset_size_ceiling = present_num_cpus;

	if (debug > 1)
		fprintf(dfp, "%d cpus, cpu%d is highest numbered\n",
			present_num_cpus, max_cpu_num);

	/*
	 * Allocate the ordered CPU topology list
	 * indexed by size of active_set
	 * each entry containes cpu# which is last
	 * onlined to complete a set of that size
	 */
	cpus = calloc(present_num_cpus, sizeof(unsigned int));
	if (cpus == NULL)
		err(1, "calloc(%d, %zd)", present_num_cpus, sizeof(unsigned int));

	/*
	 * Allocate cpuset_present, initialize to all CPUs in system
	 */
	cpuset_present = CPU_ALLOC((max_cpu_num + 1));
	if (cpuset_present == NULL)
		err(3, "CPU_ALLOC");
	system_cpuset_size = CPU_ALLOC_SIZE((max_cpu_num + 1));
	CPU_ZERO_S(system_cpuset_size, cpuset_present);
	sum_for_all_proc_cpus(cpu_mark_present, 0);

	/*
	 * Allocate cpuset_active, initialize = cpuset_present
	 */
	cpuset_active = CPU_ALLOC((max_cpu_num + 1));
	if (cpuset_active == NULL)
		err(3, "CPU_ALLOC");
	CPU_ZERO_S(system_cpuset_size, cpuset_active);
	CPU_OR_S(system_cpuset_size, cpuset_active, cpuset_present, cpuset_active);

	/*
	 * TODO: make this 2 on HT boxes
	 */
	cpuset_size_floor = 1;

	topology_init_cpu_order();
}

static int cpu_record_utilization(UNUSED(index), unsigned int cpu,
	UNUSED(a), UNUSED(b), UNUSED(c), unsigned int idle_count) 
{
	if (debug > 1)
		fprintf(dfp, "cpu%d idle %d\n", cpu, idle_count);

//	if (CPU_ISSET_S(cpu, system_cpuset_size, cpuset_active))
	return idle_count;
//	else
//		return 0;
}

static void system_snapshot_utilization(unsigned int index)
{

	history[index].seconds = timestamp_sec();
	if(debug > 1)
		fprintf(dfp, "util timestamp %f\n", history[index].seconds);

	history[index].system_idle_tick_sum =
		sum_for_all_proc_cpus(cpu_record_utilization, 0);
	if (debug > 2)
		debug_dump_history();
}

#if NOTYET
static int per_cpu_stub(unsigned int cpu)
{
	fprintf(dfp, "hello world %d\n", cpu);
	return 0;
}
#endif
/*
 * cpuset_calculate_utilization()
 *
 * return average_utilization of set during previous interval from 0.0 to 100.0 %
 */
double ema;

static double cpuset_calculate_utilization(unsigned int util_index_prev, unsigned int util_index, unsigned int active_num_cpus)
{
	double idle_ticks;
	double ticks_per_interval_per_cpu;
	double delta_sec;
	double average_utilization;
	double total_possible_ticks;
	double busy_ticks;

#if NOYET
	double ema_period_sec = 2.0;
	double ema_weight;
#endif

	if (util_index == util_index_prev)
		return -1;

	delta_sec = history[util_index].seconds - history[util_index_prev].seconds;
	debug_sleep_histogram_record(sleep_actual_histogram, delta_sec);

	if (delta_sec <= 0) {
		fprintf(dfp, "BUG: delta_sec %f\n", delta_sec);
		delta_sec = 0.01;
	}
	set_size_choosen[active_num_cpus]++;
	set_size_seconds[active_num_cpus] += delta_sec;

	if(debug > 1)
		fprintf(dfp, "delta_sec %f = [%d] %f - [%d] %f\n",
			delta_sec, util_index, history[util_index].seconds,
			util_index_prev, history[util_index_prev].seconds);

	ticks_per_interval_per_cpu = user_tick_per_sec * delta_sec;
	if(debug > 1)
		fprintf(dfp, "ticks_per_interval_per_cpu %f = %ld * %f\n",
			ticks_per_interval_per_cpu, user_tick_per_sec, delta_sec);

	idle_ticks = history[util_index].system_idle_tick_sum -
		history[util_index_prev].system_idle_tick_sum;
	if (debug > 1)
		fprintf(dfp, "idle_ticks %f = %lld - %lld\n",
			idle_ticks, history[util_index].system_idle_tick_sum,
			history[util_index_prev].system_idle_tick_sum);

	total_possible_ticks = ticks_per_interval_per_cpu * present_num_cpus;
	busy_ticks = total_possible_ticks - idle_ticks;

	if (debug > 1)
		fprintf(dfp, "total_possible_ticks %f busy_ticks %f\n",
			total_possible_ticks, busy_ticks);


	average_utilization = 100 * busy_ticks / ticks_per_interval_per_cpu / active_num_cpus;

	if (average_utilization < 0)
		average_utilization = 0;


#if NOTYET
	/*
	 * Exponential Moving Average (EMA)
	 *
	 * EMA(t) = EMA(t-1) + EMA_WEIGHT * (SAMPLE(t) - EMA(t-1))
	 *
	 * Larger EMA_WEIGHT favors SAMPLE(t)
	 * at the expense of EMA history, EMA(t-1)
	 *
	 * An N-period EMA will forget 86% of history
	 * after N samples, and EMA_WEIGHT = 1/(N + 1).
	 *
	 * We make the policy decision of selecting ema_period_sec = 2.0.
	 * We use a different EMA_WEIGHT depending on the sample rate.
	 *
	 * EMA_WEIGHT(2.0 sec, 100 samples/sec) = 2/(200+1) = 0.00995
	 * EMA_WEIGHT(2.0 sec, 10 samples/sec)  = 2/(20+1)  = 0.0952
	 * EMA_WEIGHT(2.0 sec, 1 samples/sec)  = 2/(2+1)  = 0.666
	 * EMA_WEIGHT(2.0 sec, .5 samples/sec)  = 2/(1+1)  = 1.0
	 */
	ema_weight = 2 / (ema_period_sec * 1/delta_sec + 1);
	ema = ema + ema_weight * average_utilization -  ema_weight * ema;
#endif

	if(debug) {
		char cpulist[256];

		cpulist_create(cpulist, 256, cpuset_active, system_cpuset_size);

		fprintf(dfp, "%d cpus util%%: %.2f%% TGT: %.2f sec: %.4f set: %s\n",
			active_num_cpus, average_utilization,
			active_num_cpus * average_utilization / 100,
			delta_sec, cpulist);
	}

	return average_utilization;
}
/*
 * cpuset_change_size(target_num, num_active)
 * cpu[num_active] is the next available cpu
 */
static void cpuset_change_size(unsigned int target_num, unsigned int num_active)
{
	unsigned int i;
	if (debug > 1)
		fprintf(dfp, "ACTIVE %d TARGET: %d ",
			num_active, target_num);

	if (target_num > num_active) {
		if (debug > 1) fprintf(dfp, "ADD:");
		for (i = num_active; i < target_num; ++i) {
			CPU_SET_S(cpus[i], system_cpuset_size, cpuset_active);
			if(debug > 1) fprintf(dfp, " cpu%d", cpus[i]);
		}
		if (debug > 1) fprintf(dfp, "\n");
	}
	if (target_num < num_active) {
		if (debug > 1) fprintf(dfp, "SUB:");
		for (i = num_active - 1; i > target_num - 1; --i) {
			CPU_CLR_S(cpus[i], system_cpuset_size, cpuset_active);
			if(debug > 1) fprintf(dfp, " cpu%d", cpus[i]);
		}
		if (debug > 1) fprintf(dfp, "\n");
	}
}
static void do_binding(cpu_set_t *set)
{
	int retval;
	char cpulist[256];
	FILE *fp;

	cpulist_create(cpulist, 256, set, system_cpuset_size);
	fp = fopen_or_die("balloon/cpuset.cpus", "w");
	retval = fputs(cpulist, fp);
	if (retval == EOF)
		err(1, "failed to write %s to balloon/cpuset.cpus\n", cpulist);
	
if (debug) fprintf(dfp, "balloon/cpuset.cpus %s\n", cpulist);
	retval = fclose(fp);
	if (retval)
		err(1, "fcose balloon/cpuset.cpus");
#if NOT_ANYMORE
	{
	char command[256];
	snprintf(command, 256, "taskset -cp %s all", cpulist);
	retval = system(command);
	if (debug > 1)
		fprintf(dfp, "\t\t\t\t\tSYSTEM \"%s\" = %d\n", command, retval);
	}
#endif
}

/*
 * cpuset_update()
 *
 * The "ideal" target set size is the size that could retire
 * the previous load with all CPUs exactly 100% utilized.
 * But the math rarely works out evenly, and we need to
 * decided on an integer target number of CPUs in the set.
 * 
 * Say utilization * active_num_cpus = 3.2?
 * We can't allocate 0.2 of a CPU...
 *
 */
static unsigned int cpuset_update(double avg_util, unsigned int active_num_cpus)
{
	double ideal_target_num_cpus;
	double target_num_cpus;
	double roundup;
	int truncated_int;

	if (avg_util > 95) {
		if (get_num_runnable_threads() > active_num_cpus + 2) {
			target_num_cpus = active_num_cpus + 1;
			goto done;
		}
	}
	ideal_target_num_cpus = (avg_util * active_num_cpus)/100;
	truncated_int = (unsigned int)ideal_target_num_cpus;
	roundup = ideal_target_num_cpus - truncated_int;
	if (roundup > 0.5)
		roundup = 1;
	else if (roundup > ideal_target_num_cpus/10)
		roundup = 1;
		
	target_num_cpus = ideal_target_num_cpus + roundup;

	if (debug > 1)
		fprintf(dfp, "ideal %f = %f * %d; target %d\n",
			ideal_target_num_cpus, avg_util, active_num_cpus,
			(unsigned int)target_num_cpus);

#if 0
	ideal_set_size = util_sum / 100.0;

	if (ideal_set_size > (up_threshold * active_num_cpus)) {
		/*
  		 * Utilization is above up_threshold
		 * Increase set size
		 */

		delta_set_size = active_num_cpus * up_slope;
		if (delta_set_size < 1 )
			delta_set_size == 1;

		target_set_size = active_num_cpus + increase;
	} else {
		/*
 		 * Utilization is below up_threshold
 		 * Possibly decrease set size
 		 */
		delta_set_size = active_num_cpus - ideal_set_size;
		delta_set_size *= down_rate;
		target_set_size = active_num_cpus - delta_set_size;
	}
#endif

done:
	if (target_num_cpus > cpuset_size_ceiling)
		target_num_cpus = cpuset_size_ceiling;
	else if (target_num_cpus < cpuset_size_floor)
		target_num_cpus = cpuset_size_floor;

	if ((unsigned int) target_num_cpus != active_num_cpus) {
		cpuset_change_size(target_num_cpus, active_num_cpus);
		do_binding(cpuset_active);
	}

	return (unsigned int) target_num_cpus;
}

static void main_loop(void)
{
	int i;
	unsigned int util_index_prev = 0;
	unsigned int util_index = 1;
	unsigned int active_num_cpus = present_num_cpus;	// TBD

	syslog(LOG_NOTICE, "shepherd started.");
	/*
	 * Initial snapshot
	 */
	system_snapshot_utilization(util_index_prev);
	history[util_index_prev].cpuset_num_cpus = active_num_cpus;
	sleep_for_sec(poll_fast_sec);

	/*
	 * run for(ever)
	 */
	for (i = 0; ; ++i) {
		double avg_util;

		system_snapshot_utilization(util_index);
		history[util_index].cpuset_num_cpus = active_num_cpus;
		avg_util = cpuset_calculate_utilization(util_index_prev, util_index, active_num_cpus);

		if (exit_main_loop)
			break;

		active_num_cpus = cpuset_update(avg_util, active_num_cpus);

		sleep_for_sec(get_next_polling_interval_sec(avg_util, active_num_cpus));

		util_index_prev = util_index;
		util_index += 1;
		if (util_index >= HISTORY_LENGTH)
			util_index = 0;

	}
	syslog(LOG_NOTICE, "shepherd terminated.");
}
pid_t child_pid;

/*
 * nanny - babysit the child
 * leave a note for the parrent main loop
 * if the child exits
 */
static void nanny(__attribute__((unused))int signal)
{
	if (waitpid(child_pid, NULL, WNOHANG) == child_pid)
		exit_main_loop = 1;
}
/*
 * fork_it()
 */
static void fork_it(char **argv)
{

	child_pid = fork();

	if (!child_pid) { /* child */

		if (!child_pid) { /* command child  */
			execvp(argv[0], argv);
			err(1, "%s", argv[0]);
		}
	} else { /* parent */
		signal(SIGCHLD, nanny);
	}
}
static void signal_handler_stats(int signal)
{
	if (debug)
		fprintf(dfp, "signal %d received\n", signal);

	dump_statistics();
}

static void signal_handler_end_it(int signal)
{
	if (debug)
		fprintf(dfp, "caught signal %d\n", signal);
	exit_main_loop = 1;
}

static void signals_init(void)
{
	signal(SIGALRM, signal_handler_stats);
	signal(SIGUSR1, signal_handler_stats);
	signal(SIGINT, signal_handler_end_it);
}

void write_file_value(char *path, char *val)
{
	int retval;
	FILE *fp;

	fp = fopen_or_die(path, "w");
	retval = fputs(val, fp);
	if (retval == EOF)
		err(1, "fputs %s failed", path);
	retval = fclose(fp);
	if (retval)
		err(1, "close %s", path);
}

void copy_file_by_line(char *from_path, char *to_path)
{
	FILE *from_fp, *to_fp;
	char line_buf[1024];
	char *s;
	int retval;

	from_fp = fopen_or_die(from_path, "r");
	to_fp = fopen_or_die(to_path, "w");

	while (fgets(line_buf, sizeof(line_buf), from_fp) != NULL) {

		if(debug > 1) fprintf(dfp, "copying: %s", line_buf);

		retval = fputs(line_buf, to_fp);
		if (retval == EOF)
			err(1, "fputs cpuset.mems");

		rewind(to_fp);
	}

	retval = fclose(from_fp);
	if (retval)
		err(1, "close %s", from_path);

	retval = fclose(to_fp);
	if (retval)
		err(1, "close %s", to_path);


}


static void cpuset_init(void)
{
	int retval;

	retval = access(cpuset_base, F_OK);
	if (retval) {
		if (debug)
			fprintf(dfp, "making %s\n", cpuset_base);
		retval = mkdir(cpuset_base, 0755);
		if (retval) {
			if (errno == EEXIST)
				fprintf(dfp, "okay, %s is already there\n", cpuset_base);
			else
				err(1, "could  not  create '%s'", cpuset_base);
		}
	}

	if (cgroupv2)
		retval = mount("cpuset", cpuset_base, "cgroup2", 0, NULL);
	else
		retval = mount("dummy", cpuset_base, "cgroup", 0, "cpuset");
	if (retval) {
		if (errno != EBUSY)
			err(retval, "mount cpuset");
		if (debug)
			fprintf(dfp, "cpuset already mounted\n");
	}
	retval = chdir(cpuset_base);
	if (retval)
		err(retval, "%s", cpuset_base);

	retval = mkdir(cpuset_balloon, 0755);
	if (retval) {
		if (errno == EEXIST)
			fprintf(dfp, "okay, %s is already there\n", cpuset_balloon);
		else
			err(1, "could  not  create '%s'", cpuset_balloon);
	}

	retval = mkdir(cpuset_exempt, 0755);
	if (retval) {
		if (errno == EEXIST)
			fprintf(dfp, "okay, %s is already there\n", cpuset_exempt);
		else
			err(1, "could  not  create '%s'", cpuset_exempt);
	}

	if (cgroupv2) {
		write_file_value("cgroup.subtree_control", "+cpuset");
		copy_file_by_line("cpuset.mems.effective", "balloon/cpuset.mems");
		copy_file_by_line("cpuset.cpus.effective", "balloon/cpuset.cpus");
		copy_file_by_line("cgroup.procs", "balloon/cgroup.procs");
	} else {
		copy_file_by_line("cpuset.mems", "balloon/cpuset.mems");
		copy_file_by_line("cpuset.cpus", "balloon/cpuset.cpus");
		copy_file_by_line("tasks", "balloon/tasks");
	}

	if (exempt_process)
		add_exempt_tasks();
}

void daemonize(void)
{
	pid_t pid;
	int i;

	pid = fork();
	if (pid < 0)
		err(1, "fork");
	if (pid > 0)
		exit(0);	/* parent exits */

	if (setsid() < 0)
		err(1, "setsid");
	signal(SIGCHLD, SIG_IGN);
	signal(SIGHUP, SIG_IGN);

	pid = fork();
	if (pid < 0)
		err(2, "Fork");
	if (pid > 0)
		exit(0);	/* parent exits */

	umask(0);
	chdir("/");

	for (i = sysconf(_SC_OPEN_MAX); i >= 0; i--)
		close(i);
}

void debug_init(void)
{
	if (output_path == NULL) {
		dfp = stderr;

		//output_path = "/tmp/shepherd.log";
	} else {
		dfp = fopen_or_die(output_path, "w");
	}
}

int main(int argc, char **argv)
{
	srandom((unsigned int)time(NULL));

	defaults_init();

	cmdline(argc, argv);

	debug_init();

	if (!debug)
		daemonize();

	openlog("shepherd", LOG_PID, LOG_DAEMON);

	topology_probe();

	cpuset_init();

	stats_init();

	if (argc - optind)
		fork_it(argv + optind);

	signals_init();
	main_loop();

	dump_statistics();
	do_binding(cpuset_present);	/* restore system binding */
	return 0;
}

