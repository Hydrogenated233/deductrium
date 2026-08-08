/** Serialize state-changing requests sent to one persistent Worker. */
export class TTWorkerMutationQueue {
    private pending: Promise<void> = Promise.resolve();

    enqueue(operation: () => Promise<void>) {
        const current = this.pending
            .catch(() => { })
            .then(operation);
        this.pending = current.catch(() => { });
        return current;
    }

    wait() {
        return this.pending;
    }
}
