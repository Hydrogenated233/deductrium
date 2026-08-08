/** Serialize state-changing requests sent to one persistent Worker. */
export class TTWorkerMutationQueue {
    pending = Promise.resolve();
    enqueue(operation) {
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
//# sourceMappingURL=worker-mutation-queue.js.map