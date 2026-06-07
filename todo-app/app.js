// To-Do List App with Local Storage

class TodoApp {
    constructor() {
        this.todos = [];
        this.currentFilter = 'all';
        this.editingId = null;
        
        this.init();
    }

    init() {
        this.loadFromStorage();
        this.setupEventListeners();
        this.render();
    }

    // ==================== STORAGE ====================
    
    loadFromStorage() {
        const stored = localStorage.getItem('todos');
        this.todos = stored ? JSON.parse(stored) : [];
    }

    saveToStorage() {
        localStorage.setItem('todos', JSON.stringify(this.todos));
    }

    // ==================== CRUD OPERATIONS ====================

    addTodo(text) {
        if (!text.trim()) {
            alert('Please enter a task!');
            return;
        }

        const todo = {
            id: Date.now(),
            text: text.trim(),
            completed: false,
            createdAt: new Date().toLocaleString()
        };

        this.todos.unshift(todo);
        this.saveToStorage();
        this.render();
        document.getElementById('todoInput').value = '';
    }

    deleteTodo(id) {
        this.todos = this.todos.filter(todo => todo.id !== id);
        this.saveToStorage();
        this.render();
    }

    toggleTodo(id) {
        const todo = this.todos.find(t => t.id === id);
        if (todo) {
            todo.completed = !todo.completed;
            this.saveToStorage();
            this.render();
        }
    }

    updateTodo(id, newText) {
        const todo = this.todos.find(t => t.id === id);
        if (todo) {
            todo.text = newText.trim();
            this.saveToStorage();
            this.editingId = null;
            this.render();
        }
    }

    startEditingTodo(id) {
        this.editingId = id;
        this.render();
        
        // Focus on the input field
        setTimeout(() => {
            const input = document.getElementById(`edit-input-${id}`);
            if (input) input.focus();
        }, 0);
    }

    cancelEditingTodo() {
        this.editingId = null;
        this.render();
    }

    clearCompleted() {
        if (confirm('Are you sure you want to clear all completed tasks?')) {
            this.todos = this.todos.filter(todo => !todo.completed);
            this.saveToStorage();
            this.render();
        }
    }

    clearAll() {
        if (confirm('Are you sure you want to delete ALL tasks?')) {
            this.todos = [];
            this.saveToStorage();
            this.render();
        }
    }

    // ==================== FILTERING ====================

    setFilter(filter) {
        this.currentFilter = filter;
        this.render();
    }

    getFilteredTodos() {
        switch(this.currentFilter) {
            case 'active':
                return this.todos.filter(todo => !todo.completed);
            case 'completed':
                return this.todos.filter(todo => todo.completed);
            case 'all':
            default:
                return this.todos;
        }
    }

    // ==================== STATISTICS ====================

    getStats() {
        const total = this.todos.length;
        const completed = this.todos.filter(t => t.completed).length;
        const active = total - completed;

        return { total, completed, active };
    }

    // ==================== RENDERING ====================

    renderTodos() {
        const todoList = document.getElementById('todoList');
        const emptyState = document.getElementById('emptyState');
        const filteredTodos = this.getFilteredTodos();

        todoList.innerHTML = '';

        if (filteredTodos.length === 0) {
            emptyState.classList.add('show');
            return;
        }

        emptyState.classList.remove('show');

        filteredTodos.forEach(todo => {
            const li = document.createElement('li');
            li.className = `todo-item ${todo.completed ? 'completed' : ''}`;
            li.id = `todo-${todo.id}`;

            if (this.editingId === todo.id) {
                // Edit mode
                li.innerHTML = `
                    <input 
                        type="text" 
                        id="edit-input-${todo.id}" 
                        class="edit-input" 
                        value="${this.escapeHtml(todo.text)}"
                    >
                    <button class="save-btn">Save</button>
                    <button class="cancel-btn">Cancel</button>
                `;

                li.querySelector('.save-btn').addEventListener('click', () => {
                    const newText = li.querySelector(`#edit-input-${todo.id}`).value;
                    this.updateTodo(todo.id, newText);
                });

                li.querySelector('.cancel-btn').addEventListener('click', () => {
                    this.cancelEditingTodo();
                });

                // Enter to save, Escape to cancel
                li.querySelector(`#edit-input-${todo.id}`).addEventListener('keydown', (e) => {
                    if (e.key === 'Enter') {
                        const newText = li.querySelector(`#edit-input-${todo.id}`).value;
                        this.updateTodo(todo.id, newText);
                    } else if (e.key === 'Escape') {
                        this.cancelEditingTodo();
                    }
                });
            } else {
                // Display mode
                li.innerHTML = `
                    <input 
                        type="checkbox" 
                        class="checkbox" 
                        ${todo.completed ? 'checked' : ''}
                    >
                    <span class="todo-text">${this.escapeHtml(todo.text)}</span>
                    <div class="todo-actions">
                        <button class="edit-btn">Edit</button>
                        <button class="delete-btn">Delete</button>
                    </div>
                `;

                li.querySelector('.checkbox').addEventListener('change', () => {
                    this.toggleTodo(todo.id);
                });

                li.querySelector('.edit-btn').addEventListener('click', () => {
                    this.startEditingTodo(todo.id);
                });

                li.querySelector('.delete-btn').addEventListener('click', () => {
                    if (confirm('Are you sure you want to delete this task?')) {
                        this.deleteTodo(todo.id);
                    }
                });
            }

            todoList.appendChild(li);
        });
    }

    updateStats() {
        const { total, completed, active } = this.getStats();
        document.getElementById('totalCount').textContent = total;
        document.getElementById('activeCount').textContent = active;
        document.getElementById('completedCount').textContent = completed;
    }

    updateFilterButtons() {
        document.querySelectorAll('.filter-btn').forEach(btn => {
            btn.classList.remove('active');
            if (btn.dataset.filter === this.currentFilter) {
                btn.classList.add('active');
            }
        });
    }

    render() {
        this.renderTodos();
        this.updateStats();
        this.updateFilterButtons();
    }

    escapeHtml(text) {
        const div = document.createElement('div');
        div.textContent = text;
        return div.innerHTML;
    }

    // ==================== EVENT LISTENERS ====================

    setupEventListeners() {
        // Add todo
        document.getElementById('addBtn').addEventListener('click', () => {
            const input = document.getElementById('todoInput');
            this.addTodo(input.value);
        });

        document.getElementById('todoInput').addEventListener('keypress', (e) => {
            if (e.key === 'Enter') {
                this.addTodo(e.target.value);
            }
        });

        // Filter buttons
        document.querySelectorAll('.filter-btn').forEach(btn => {
            btn.addEventListener('click', (e) => {
                this.setFilter(e.target.dataset.filter);
            });
        });

        // Clear buttons
        document.getElementById('clearCompleted').addEventListener('click', () => {
            this.clearCompleted();
        });

        document.getElementById('clearAll').addEventListener('click', () => {
            this.clearAll();
        });
    }
}

// Initialize the app when the DOM is loaded
document.addEventListener('DOMContentLoaded', () => {
    window.app = new TodoApp();
});
