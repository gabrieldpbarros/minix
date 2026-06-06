/* This file contains the scheduling policy for SCHED
 *
 * The entry points are:
 *   do_noquantum:        Called on behalf of process' that run out of quantum
 *   do_start_scheduling  Request to start scheduling a proc
 *   do_stop_scheduling   Request to stop scheduling a proc
 *   do_nice		  Request to change the nice level on a proc
 *   init_scheduling      Called from main.c to set up/prepare scheduling
 */
#include "sched.h"
#include "schedproc.h"
#include <assert.h>
#include <minix/com.h>
#include <machine/archtypes.h>

static unsigned balance_timeout;

#define BALANCE_TIMEOUT	5 /* how often to balance queues in seconds */

static int schedule_process(struct schedproc * rmp, unsigned flags);

#define SCHEDULE_CHANGE_PRIO	0x1
#define SCHEDULE_CHANGE_QUANTUM	0x2
#define SCHEDULE_CHANGE_CPU	0x4

#define SCHEDULE_CHANGE_ALL	(	\
		SCHEDULE_CHANGE_PRIO	|	\
		SCHEDULE_CHANGE_QUANTUM	|	\
		SCHEDULE_CHANGE_CPU		\
		)

#define schedule_process_local(p)	\
	schedule_process(p, SCHEDULE_CHANGE_PRIO | SCHEDULE_CHANGE_QUANTUM)
#define schedule_process_migrate(p)	\
	schedule_process(p, SCHEDULE_CHANGE_CPU)

#define CPU_DEAD	-1

#define cpu_is_available(c)	(cpu_proc[c] >= 0)

#define DEFAULT_USER_TIME_SLICE 200

/* SRTN usando média móvel exponencial.
 *
 * O servidor SCHED não conhece exatamente o próximo burst de CPU
 * de um processo. Por isso, estimamos o próximo burst com:
 *
 *   tau(n+1) = alpha * t(n) + (1 - alpha) * tau(n)
 *
 * Para evitar o uso de ponto flutuante no servidor do sistema,
 * alpha é representado como SRTN_ALPHA_NUM / SRTN_ALPHA_DEN.
 */
#define SRTN_ALPHA_NUM		1
#define SRTN_ALPHA_DEN		2
#define SRTN_MIN_BURST		1
#define SRTN_DEFAULT_BURST	DEFAULT_USER_TIME_SLICE

static void srtn_init_proc(struct schedproc *rmp, struct schedproc *parent);
static void srtn_charge_quantum(struct schedproc *rmp);
static void srtn_recalculate_user_priorities(void);
static int srtn_cmp_remaining(const struct schedproc *a,
	const struct schedproc *b);


/* processes created by RS are sysytem processes */
#define is_system_proc(p)	((p)->parent == RS_PROC_NR)

static unsigned cpu_proc[CONFIG_MAX_CPUS];

static void pick_cpu(struct schedproc * proc)
{
#ifdef CONFIG_SMP
	unsigned cpu, c;
	unsigned cpu_load = (unsigned) -1;
	
	if (machine.processors_count == 1) {
		proc->cpu = machine.bsp_id;
		return;
	}

	/* schedule sysytem processes only on the boot cpu */
	if (is_system_proc(proc)) {
		proc->cpu = machine.bsp_id;
		return;
	}

	/* if no other cpu available, try BSP */
	cpu = machine.bsp_id;
	for (c = 0; c < machine.processors_count; c++) {
		/* skip dead cpus */
		if (!cpu_is_available(c))
			continue;
		if (c != machine.bsp_id && cpu_load > cpu_proc[c]) {
			cpu_load = cpu_proc[c];
			cpu = c;
		}
	}
	proc->cpu = cpu;
	cpu_proc[cpu]++;
#else
	proc->cpu = 0;
#endif
}


/*===========================================================================*
 *				srtn_init_proc				     *
 *===========================================================================*/
static void srtn_init_proc(struct schedproc *rmp, struct schedproc *parent)
{
	if (parent != NULL && (parent->flags & IN_USE)) {
		rmp->estimated_burst = parent->estimated_burst;
		if (rmp->estimated_burst < SRTN_MIN_BURST)
			rmp->estimated_burst = SRTN_DEFAULT_BURST;
	} else {
		rmp->estimated_burst = SRTN_DEFAULT_BURST;
	}

	rmp->remaining_time = rmp->estimated_burst;
	rmp->current_burst = 0;
}

/*===========================================================================*
 *				srtn_charge_quantum			     *
 *===========================================================================*/
static void srtn_charge_quantum(struct schedproc *rmp)
{
	unsigned used;

	/* do_noquantum() é chamada apenas depois que o processo usa todo
	 * o quantum que foi atribuído a ele. Portanto, a melhor informação
	 * disponível aqui é o tamanho do quantum configurado.
	 */
	used = rmp->time_slice;
	if (used < SRTN_MIN_BURST)
		used = SRTN_MIN_BURST;

	rmp->current_burst += used;

	if (rmp->remaining_time > used) {
		rmp->remaining_time -= used;
		return;
	}

	/* O burst previsto terminou. Calcula a próxima estimativa usando EMA. */
	rmp->estimated_burst =
		((SRTN_ALPHA_NUM * rmp->current_burst) +
		((SRTN_ALPHA_DEN - SRTN_ALPHA_NUM) * rmp->estimated_burst)) /
		SRTN_ALPHA_DEN;

	if (rmp->estimated_burst < SRTN_MIN_BURST)
		rmp->estimated_burst = SRTN_MIN_BURST;

	rmp->remaining_time = rmp->estimated_burst;
	rmp->current_burst = 0;
}

/*===========================================================================*
 *				srtn_cmp_remaining			     *
 *===========================================================================*/
static int srtn_cmp_remaining(const struct schedproc *a,
	const struct schedproc *b)
{
	if (a->remaining_time < b->remaining_time)
		return -1;
	if (a->remaining_time > b->remaining_time)
		return 1;

	/* Critério de desempate: preserva, tanto quanto possível, o processo
	 * que esperou ou iniciou primeiro usando a ordem dos endpoints.
	 * Isso mantém o resultado estável.
	 */
	if (a->endpoint < b->endpoint)
		return -1;
	if (a->endpoint > b->endpoint)
		return 1;

	return 0;
}

/*===========================================================================*
 *			srtn_recalculate_user_priorities		     *
 *===========================================================================*/
static void srtn_recalculate_user_priorities(void)
{
	struct schedproc *ordered[NR_PROCS];
	struct schedproc *rmp;
	int count, i, j, proc_nr;

	count = 0;

	/* Apenas processos de usuário são tratados por esta política SRTN.
	 * Processos do sistema mantêm suas prioridades normais, o que é
	 * mais seguro para o MINIX.
	 */
	for (proc_nr = 0, rmp = schedproc; proc_nr < NR_PROCS;
	    proc_nr++, rmp++) {
		if (!(rmp->flags & IN_USE))
			continue;
		if (is_system_proc(rmp))
			continue;

		ordered[count++] = rmp;
	}

	/* Ordenação por inserção simples: NR_PROCS é pequeno e esta função
	 * roda apenas quando o SCHED é notificado, não a cada interrupção
	 * do temporizador.
	 */
	for (i = 1; i < count; i++) {
		struct schedproc *key = ordered[i];
		j = i - 1;

		while (j >= 0 && srtn_cmp_remaining(key, ordered[j]) < 0) {
			ordered[j + 1] = ordered[j];
			j--;
		}
		ordered[j + 1] = key;
	}

	for (i = 0; i < count; i++) {
		unsigned new_q;

		new_q = USER_Q + i;
		if (new_q > MIN_USER_Q)
			new_q = MIN_USER_Q;

		/* Respeita nice/max_priority. No MINIX, um número menor de fila
		 * significa maior prioridade de escalonamento.
		 */
		if (new_q < ordered[i]->max_priority)
			new_q = ordered[i]->max_priority;

		if (ordered[i]->priority != new_q) {
			ordered[i]->priority = new_q;
			schedule_process_local(ordered[i]);
		}
	}
}


/*===========================================================================*
 *				do_noquantum				     *
 *===========================================================================*/

int do_noquantum(message *m_ptr)
{
	register struct schedproc *rmp;
	int rv, proc_nr_n;

	if (sched_isokendpt(m_ptr->m_source, &proc_nr_n) != OK) {
		printf("SCHED: WARNING: got an invalid endpoint in OOQ msg %u.\n",
		m_ptr->m_source);
		return EBADEPT;
	}

	rmp = &schedproc[proc_nr_n];

	/* SRTN: em vez de diminuir a prioridade do processo como no
	 * escalonador padrão, atualiza o tempo restante previsto e depois
	 * reordena os processos de usuário pelo menor tempo restante.
	 */
	srtn_charge_quantum(rmp);
	srtn_recalculate_user_priorities();

	if ((rv = schedule_process_local(rmp)) != OK) {
		return rv;
	}
	return OK;
}

/*===========================================================================*
 *				do_stop_scheduling			     *
 *===========================================================================*/
int do_stop_scheduling(message *m_ptr)
{
	register struct schedproc *rmp;
	int proc_nr_n;

	/* check who can send you requests */
	if (!accept_message(m_ptr))
		return EPERM;

	if (sched_isokendpt(m_ptr->m_lsys_sched_scheduling_stop.endpoint,
		    &proc_nr_n) != OK) {
		printf("SCHED: WARNING: got an invalid endpoint in OOQ msg "
		"%d\n", m_ptr->m_lsys_sched_scheduling_stop.endpoint);
		return EBADEPT;
	}

	rmp = &schedproc[proc_nr_n];
#ifdef CONFIG_SMP
	cpu_proc[rmp->cpu]--;
#endif
	rmp->flags = 0; /*&= ~IN_USE;*/

	return OK;
}

/*===========================================================================*
 *				do_start_scheduling			     *
 *===========================================================================*/
int do_start_scheduling(message *m_ptr)
{
	register struct schedproc *rmp;
	int rv, proc_nr_n, parent_nr_n;
	
	/* we can handle two kinds of messages here */
	assert(m_ptr->m_type == SCHEDULING_START || 
		m_ptr->m_type == SCHEDULING_INHERIT);

	/* check who can send you requests */
	if (!accept_message(m_ptr))
		return EPERM;

	/* Resolve endpoint to proc slot. */
	if ((rv = sched_isemtyendpt(m_ptr->m_lsys_sched_scheduling_start.endpoint,
			&proc_nr_n)) != OK) {
		return rv;
	}
	rmp = &schedproc[proc_nr_n];

	/* Populate process slot */
	rmp->endpoint     = m_ptr->m_lsys_sched_scheduling_start.endpoint;
	rmp->parent       = m_ptr->m_lsys_sched_scheduling_start.parent;
	rmp->max_priority = m_ptr->m_lsys_sched_scheduling_start.maxprio;
	if (rmp->max_priority >= NR_SCHED_QUEUES) {
		return EINVAL;
	}

	/* Inherit current priority and time slice from parent. Since there
	 * is currently only one scheduler scheduling the whole system, this
	 * value is local and we assert that the parent endpoint is valid */
	if (rmp->endpoint == rmp->parent) {
		/* We have a special case here for init, which is the first
		   process scheduled, and the parent of itself. */
		rmp->priority   = USER_Q;
		rmp->time_slice = DEFAULT_USER_TIME_SLICE;

		/*
		 * Since kernel never changes the cpu of a process, all are
		 * started on the BSP and the userspace scheduling hasn't
		 * changed that yet either, we can be sure that BSP is the
		 * processor where the processes run now.
		 */
#ifdef CONFIG_SMP
		rmp->cpu = machine.bsp_id;
		/* FIXME set the cpu mask */
#endif
	}
	
	switch (m_ptr->m_type) {

	case SCHEDULING_START:
		/* We have a special case here for system processes, for which
		 * quanum and priority are set explicitly rather than inherited 
		 * from the parent */
		rmp->priority   = rmp->max_priority;
		rmp->time_slice = m_ptr->m_lsys_sched_scheduling_start.quantum;
		break;
		
	case SCHEDULING_INHERIT:
		/* Inherit current priority and time slice from parent. Since there
		 * is currently only one scheduler scheduling the whole system, this
		 * value is local and we assert that the parent endpoint is valid */
		if ((rv = sched_isokendpt(m_ptr->m_lsys_sched_scheduling_start.parent,
				&parent_nr_n)) != OK)
			return rv;

		rmp->priority = schedproc[parent_nr_n].priority;
		rmp->time_slice = schedproc[parent_nr_n].time_slice;
		break;
		
	default: 
		/* not reachable */
		assert(0);
	}

	if (m_ptr->m_type == SCHEDULING_INHERIT)
		srtn_init_proc(rmp, &schedproc[parent_nr_n]);
	else
		srtn_init_proc(rmp, NULL);

	/* Take over scheduling the process. The kernel reply message populates
	 * the processes current priority and its time slice */
	if ((rv = sys_schedctl(0, rmp->endpoint, 0, 0, 0)) != OK) {
		printf("Sched: Error taking over scheduling for %d, kernel said %d\n",
			rmp->endpoint, rv);
		return rv;
	}
	rmp->flags = IN_USE;

	/* Schedule the process, giving it some quantum */
	pick_cpu(rmp);
	while ((rv = schedule_process(rmp, SCHEDULE_CHANGE_ALL)) == EBADCPU) {
		/* don't try this CPU ever again */
		cpu_proc[rmp->cpu] = CPU_DEAD;
		pick_cpu(rmp);
	}

	if (rv != OK) {
		printf("Sched: Error while scheduling process, kernel replied %d\n",
			rv);
		return rv;
	}

	srtn_recalculate_user_priorities();

	/* Mark ourselves as the new scheduler.
	 * By default, processes are scheduled by the parents scheduler. In case
	 * this scheduler would want to delegate scheduling to another
	 * scheduler, it could do so and then write the endpoint of that
	 * scheduler into the "scheduler" field.
	 */

	m_ptr->m_sched_lsys_scheduling_start.scheduler = SCHED_PROC_NR;

	return OK;
}

/*===========================================================================*
 *				do_nice					     *
 *===========================================================================*/
int do_nice(message *m_ptr)
{
	struct schedproc *rmp;
	int rv;
	int proc_nr_n;
	unsigned new_q, old_q, old_max_q;

	/* check who can send you requests */
	if (!accept_message(m_ptr))
		return EPERM;

	if (sched_isokendpt(m_ptr->m_pm_sched_scheduling_set_nice.endpoint, &proc_nr_n) != OK) {
		printf("SCHED: WARNING: got an invalid endpoint in OoQ msg "
		"%d\n", m_ptr->m_pm_sched_scheduling_set_nice.endpoint);
		return EBADEPT;
	}

	rmp = &schedproc[proc_nr_n];
	new_q = m_ptr->m_pm_sched_scheduling_set_nice.maxprio;
	if (new_q >= NR_SCHED_QUEUES) {
		return EINVAL;
	}

	/* Store old values, in case we need to roll back the changes */
	old_q     = rmp->priority;
	old_max_q = rmp->max_priority;

	/* Update the proc entry and reschedule the process */
	rmp->max_priority = rmp->priority = new_q;

	if ((rv = schedule_process_local(rmp)) != OK) {
		/* Something went wrong when rescheduling the process, roll
		 * back the changes to proc struct */
		rmp->priority     = old_q;
		rmp->max_priority = old_max_q;
	}

	return rv;
}

/*===========================================================================*
 *				schedule_process			     *
 *===========================================================================*/
static int schedule_process(struct schedproc * rmp, unsigned flags)
{
	int err;
	int new_prio, new_quantum, new_cpu, niced;

	pick_cpu(rmp);

	if (flags & SCHEDULE_CHANGE_PRIO)
		new_prio = rmp->priority;
	else
		new_prio = -1;

	if (flags & SCHEDULE_CHANGE_QUANTUM)
		new_quantum = rmp->time_slice;
	else
		new_quantum = -1;

	if (flags & SCHEDULE_CHANGE_CPU)
		new_cpu = rmp->cpu;
	else
		new_cpu = -1;

	niced = (rmp->max_priority > USER_Q);

	if ((err = sys_schedule(rmp->endpoint, new_prio,
		new_quantum, new_cpu, niced)) != OK) {
		printf("PM: An error occurred when trying to schedule %d: %d\n",
		rmp->endpoint, err);
	}

	return err;
}


/*===========================================================================*
 *				init_scheduling				     *
 *===========================================================================*/
void init_scheduling(void)
{
	int r;

	balance_timeout = BALANCE_TIMEOUT * sys_hz();

	if ((r = sys_setalarm(balance_timeout, 0)) != OK)
		panic("sys_setalarm failed: %d", r);
}

/*===========================================================================*
 *				balance_queues				     *
 *===========================================================================*/

/* This function in called every N ticks to rebalance the queues. The current
 * scheduler bumps processes down one priority when ever they run out of
 * quantum. This function will find all proccesses that have been bumped down,
 * and pulls them back up. This default policy will soon be changed.
 */
void balance_queues(void)
{
	int r;

	/* O escalonador padrão aumenta periodicamente a prioridade dos
	 * processos que foram rebaixados após usarem seu quantum. O SRTN
	 * não usa essa política de envelhecimento; em vez disso, as
	 * prioridades são derivadas de remaining_time.
	 */
	srtn_recalculate_user_priorities();

	if ((r = sys_setalarm(balance_timeout, 0)) != OK)
		panic("sys_setalarm failed: %d", r);
}
