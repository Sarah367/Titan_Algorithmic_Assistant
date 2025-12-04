import tkinter as tk
from tkinter import ttk, messagebox
import random
import math
from collections import deque
import heapq
import time
import PyPDF2
import docx
from tkinter import filedialog

class CampusNavigationSystem:
    def __init__(self, parent_frame):
        self.root = parent_frame

        # graph the data structures to represent the campus
        self.nodes = {} # dictionary to store buildings
        self.edges = {} # dictionary to store paths
        self.node_counter = 0
        self.resizing_node = None

        # Visualization settings...
        self.node_radius = 40
        self.colors = {
            "node": "lightblue",
            "edge": "black",
            "mst_edge": "purple",
            "dijkstra_path": "blue",
            "bfs_path": "green",
            "dfs_path": "orange"
        }

        # algo state
        self.visited_order = []
        self.path = []
        self.mst_edges = []
        self.current_algorithm = None
        self.dragging_node = None

        # create GUI
        self.create_gui()
    
    def pack(self, **kwargs):
        self.root.pack(**kwargs)

    def create_gui(self):
        # main_container = ttk.Frame(self.root)
        # main_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        # left panel for controls
        left_container = ttk.Frame(self.root, width=300)
        left_container.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        left_container.pack_propagate(False) # prevents resizing

        self.canvas = tk.Canvas(self.root, bg="white", width=800, height=700)
        self.canvas.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        # building creation section
        node_frame = ttk.LabelFrame(left_container, text = "Building Creation")
        node_frame.pack(fill=tk.X, pady=(0, 10))

        ttk.Label(node_frame, text="Building Name:").pack(anchor = tk.W)
        self.node_name_var = tk.StringVar()
        ttk.Entry(node_frame, textvariable=self.node_name_var).pack(fill=tk.X, pady=(0, 5))
        ttk.Button(node_frame, text="Add Building", command=self.add_node).pack(fill=tk.X)

        # path creation section...
        edge_frame = ttk.LabelFrame(left_container, text = "Path Creation")
        edge_frame.pack(fill=tk.X, pady=(0, 10))

        ttk.Label(edge_frame, text="Start Building:").pack(anchor = tk.W)
        self.start_node_var = tk.StringVar()
        self.start_node_combo = ttk.Combobox(edge_frame, textvariable=self.start_node_var, state="readonly")
        self.start_node_combo.pack(fill=tk.X, pady=(0, 5))

        ttk.Label(edge_frame, text="End Building:").pack(anchor = tk.W)
        self.end_node_var = tk.StringVar()
        self.end_node_combo = ttk.Combobox(edge_frame, textvariable=self.end_node_var, state="readonly")
        self.end_node_combo.pack(fill=tk.X, pady=(0, 5))

        ttk.Label(edge_frame, text="Distance (meters):").pack(anchor = tk.W)
        self.distance_var = tk.StringVar(value = "100")
        ttk.Entry(edge_frame, textvariable=self.distance_var).pack(fill=tk.X, pady=(0, 5))

        ttk.Button(edge_frame, text="Connect Buildings", command=self.add_edge).pack(fill=tk.X)

        # algorithm section...
        algo_frame = ttk.LabelFrame(left_container, text = "Path Finding Algorithms")
        algo_frame.pack(fill=tk.X, pady=(0, 10))

        ttk.Label(algo_frame, text="Start Building:").pack(anchor=tk.W)
        self.start_path_var = tk.StringVar()
        self.start_path_combo = ttk.Combobox(algo_frame, textvariable=self.start_path_var, state="readonly")
        self.start_path_combo.pack(fill=tk.X, pady=(0, 5))

        ttk.Label(algo_frame, text="End Building:").pack(anchor=tk.W)
        self.end_path_var = tk.StringVar()
        self.end_path_combo = ttk.Combobox(algo_frame, textvariable=self.end_path_var, state="readonly")
        self.end_path_combo.pack(fill=tk.X, pady=(0, 5))

        #algo buttons
        button_frame = ttk.Frame(algo_frame)
        button_frame.pack(fill=tk.X, pady=5)

        ttk.Button(button_frame, text="BFS", command=self.run_bfs).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0,2))
        ttk.Button(button_frame, text="DFS", command=self.run_dfs).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2,2))
        ttk.Button(button_frame, text="Dijkstra", command=self.run_dijkstra).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2,0))

        mst_button_frame = ttk.Frame(algo_frame)
        mst_button_frame.pack(fill=tk.X, pady=5)
        ttk.Button(mst_button_frame, text="Prim's MST", command=self.run_prim).pack(fill=tk.X)

        # controls section
        control_frame = ttk.LabelFrame(left_container, text = "Controls")
        control_frame.pack(fill=tk.X, pady=(0, 10))

        ttk.Button(control_frame, text="Clear Visualization", command=self.clear_visualization).pack(fill=tk.X, pady=(0, 5))
        ttk.Button(control_frame, text="Reset Campus", command=self.reset_graph).pack(fill=tk.X)

        # status display
        self.status_var = tk.StringVar(value = "Add buildings to begin...")
        status_label = ttk.Label(left_container, textvariable=self.status_var, relief=tk.SUNKEN)
        status_label.pack(fill=tk.X, side=tk.BOTTOM, pady=(10, 0))

        # bind mouse for dragging the nodes.
        self.canvas.bind("<ButtonPress-1>", self.start_drag)
        self.canvas.bind("<B1-Motion>", self.drag_node)
        self.canvas.bind("<ButtonRelease-1>", self.stop_drag)

        # initialize combo boxes + results
        self.update_combo_boxes()
        self.results_window = None
    
    def show_results_window(self, results_text):
        if self.results_window and self.results_window.winfo_exists():
            self.results_window.destroy()
        
        self.results_window = tk.Toplevel(self.root)
        self.results_window.title("Algorithm Results")
        self.results_window.geometry("400x300")

        results_frame = ttk.Frame(self.results_window)
        results_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        title_label = ttk.Label(results_frame, text="Algorithm Results", font=("Arial", 13, "bold"))
        title_label.pack(pady=(0, 10))

        text_frame = ttk.Frame(results_frame)
        text_frame.pack(fill=tk.BOTH, expand=True)

        results_text_widget = tk.Text(text_frame, wrap=tk.WORD, font=("Arial", 10))
        results_text_widget.insert(1.0, results_text)
        results_text_widget.config(state=tk.DISABLED)

        text_scrollbar = ttk.Scrollbar(text_frame, orient=tk.VERTICAL, command=results_text_widget.yview)
        results_text_widget.config(yscrollcommand=text_scrollbar.set)

        results_text_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        text_scrollbar.pack(side = tk.RIGHT, fill=tk.Y)

        close_button = ttk.Button(results_frame, text="Close", command=self.results_window.destroy)
        close_button.pack(pady=(10, 0))

    def update_combo_boxes(self):
        node_names = list(self.nodes.keys())
        self.start_node_combo['values'] = node_names
        self.end_node_combo['values'] = node_names
        self.start_path_combo['values'] = node_names
        self.end_path_combo['values'] = node_names

    def add_node(self):
        name = self.node_name_var.get().strip()

        if not name: 
            messagebox.showerror("Input Error", "Building name cannot be empty.")
            return

        if name in self.nodes:
            messagebox.showerror("Input Error", f"Building '{name}' already exists.")
            return

        # place nodes with spacing between
        self.nodes[name] = (100 + self.node_counter * 80, 100 + (self.node_counter % 5) * 80)
        self.node_counter += 1
        self.edges[name] = {}

        self.update_combo_boxes()
        self.draw_graph()
        self.node_name_var.set("")
        self.status_var.set(f"Added building: {name}")

    def start_drag(self, event):
        # detect if shift is being held
        is_shift = bool(event.state & 0x0001)

        for node, (x,y) in self.nodes.items():
            distance = math.sqrt((x-event.x)**2 + (y-event.y)**2)

            # if clicking inside the circle...
            if distance <= self.node_radius:
                # if doing shift (so shift + click)
                if is_shift:
                    # then resize the node!
                    self.resizing_node = node
                    return
                
                # otherwise revert back to normal dragging...
                self.dragging_node = node
                self.drag_offset_x = x-event.x
                self.drag_offset_y = y - event.y
                return

    def drag_node(self, event):
        if self.resizing_node:
            node = self.resizing_node
            x, y = self.nodes[node]
            # the new radius is the distance from the center
            new_radius = int(math.sqrt((x-event.x)**2 + (y-event.y)**2))

            # clamp the size so that the nodes aren't too small or large
            new_radius = max(10, min(new_radius,100))

            self.node_radius = new_radius
            self.draw_graph()
            return
        
        # normal dragging
        if self.dragging_node:
            new_x = event.x + self.drag_offset_x
            new_y = event.y + self.drag_offset_y
            self.nodes[self.dragging_node] = (new_x, new_y)
            self.draw_graph()
            return
    
    def stop_drag(self, event):
        self.resizing_node = None
        self.dragging_node = None
    
    def add_edge(self):
        start = self.start_node_var.get()
        end = self.end_node_var.get()
        
        if not start or not end:
            messagebox.showerror("Input Error", "Both start and end buildings must be selected.")
            return

        if start == end:
            messagebox.showerror("Input Error", "Cannot connect a building to itself.")
            return

        try:
            distance = float(self.distance_var.get())
            if distance <= 0:
                raise ValueError("Distance must be positive.")
        except ValueError:
            messagebox.showerror("Input Error", "Distance must be a positive number!")
            return
        # undirected graph so add both ways.
        self.edges[start][end] = distance
        self.edges[end][start] = distance

        self.draw_graph()
        self.status_var.set(f"Connected {start} to {end} with distance {distance} meters.")
    
    def draw_graph(self):
        self.canvas.delete("all")

        # draw edges
        for start_node, neighbors in self.edges.items():
            if start_node not in self.nodes:
                continue

            start_x, start_y = self.nodes[start_node]

            for end_node, distance in neighbors.items():
                if end_node not in self.nodes:
                    continue

                end_x, end_y = self.nodes[end_node]

                # check if edge is part of current visualization
                edge_color = self.colors["edge"]
                edge_width = 2

                # check if edge is part of MST
                is_mst_edge = any((start_node == u and end_node == v) or (start_node == v and end_node == u)
                        for u, v, _ in self.mst_edges)

                if is_mst_edge:
                    edge_color = self.colors["mst_edge"]
                    edge_width = 4
                # path edges are checked if they are NOT mst and there's an active path algorithm running...
                elif self.path and self.current_algorithm in ["Dijkstra", "BFS", "DFS"]:
                    is_path_edge = any(
                        (start_node == self.path[i] and end_node == self.path[i+1]) or
                        (start_node == self.path[i+1] and end_node == self.path[i])
                        for i in range(len(self.path)-1)
                    )
                    if is_path_edge:
                        if self.current_algorithm == "Dijkstra":
                            edge_color = self.colors["dijkstra_path"]
                        elif self.current_algorithm == "BFS":
                            edge_color = self.colors["bfs_path"]
                        else: # only option left is dfs
                            edge_color = self.colors["dfs_path"]
                        edge_width = 4
                # draw edge
                self.canvas.create_line(start_x, start_y, end_x, end_y, fill=edge_color, width=edge_width, tags="edge")

                # draw the distance label
                mid_x = (start_x + end_x) / 2
                mid_y = (start_y + end_y) / 2
                self.canvas.create_text(
                    mid_x, mid_y,
                    text=f"{distance:.0f}m",
                    fill=edge_color, font=("Arial", 10)
                )
        # draw nodes
        for node, (x, y) in self.nodes.items():
            # determine fill color based on state
            if self.path and self.current_algorithm in ["BFS", "DFS", "Dijkstra"] and node in self.path:
                fill_color = "yellow"
            else:
                fill_color = self.colors["node"]
            
            # draw nodes
            self.canvas.create_oval(
                x - self.node_radius, y - self.node_radius,
                x + self.node_radius, y + self.node_radius,
                fill=fill_color, outline="black", width=2, tags="node"
            )

            # draw node labels
            self.canvas.create_text(
                x, y,
                text=node,
                font=("Arial", 10, "bold"),
                tags = "node_label"
            )
    
    def clear_visualization(self):
        self.visited_order = []
        self.path = []
        self.mst_edges = []
        self.current_algorithm = None
        print(f"after clearing: mst_edges={self.mst_edges}, path={self.path}")
        self.draw_graph()
        self.status_var.set("Cleared visualization.")
    
    def reset_graph(self):
        self.nodes = {}
        self.edges = {}
        self.node_counter = 0
        self.visited_order = []
        self.path = []
        self.mst_edges = []
        self.current_algorithm = None
        self.update_combo_boxes()
        self.draw_graph()
        self.status_var.set("Reset campus navigation system.")
    
    def run_bfs(self):
        self.current_algorithm = "BFS"
        start = self.start_path_var.get()
        end = self.end_path_var.get()
        self.find_path(start, end, self.bfs)
    
    def bfs(self, start, end):
        visited = []
        queue = deque([(start, [start])])

        while queue:
            current, path = queue.popleft()
            if current == end:
                return True, path, visited
            if current not in visited:
                visited.append(current)
                neighbors = sorted(self.edges.get(current, {}).keys())
                for neighbor in neighbors:
                    if neighbor not in visited:
                        queue.append((neighbor, path + [neighbor]))
        return False, [], visited

    # dfs algo
    def run_dfs(self):
        self.current_algorithm = "DFS"
        start = self.start_path_var.get()
        end = self.end_path_var.get()
        self.find_path(start, end, self.dfs)

    def dfs(self, start, end):
        visited = []
        stack = [(start, [start])]

        while stack:
            current, path = stack.pop()
            if current == end:
                return True, path, visited
            if current not in visited:
                visited.append(current)
                # get neighbors in reversed order for consistent traversal
                neighbors = sorted(self.edges.get(current, {}).keys(), reverse=True)
                for neighbor in neighbors:
                    if neighbor not in visited:
                        stack.append((neighbor, path + [neighbor]))
        return False, [], visited

    def find_path(self,start,end,algorithm_func):
        if not start or not end:
            messagebox.showerror("Input Error", "Both start and end buildings must be selected.")
            return

        if start not in self.nodes or end not in self.nodes:
            messagebox.showerror("Input Error", "Selected buildings do not exist.")
            return

        # clear previous visualization 
        self.visited_order = []
        self.path = []
        self.mst_edges = [] # also clear the mst edges if the user ran mst before

        path_found, path, visited = algorithm_func(start, end)

        self.visited_order = visited
        self.path = path if path_found else []
        self.draw_graph()

        # results display
        results_text = f"{self.current_algorithm} Results:\n\n"
        if path_found:
            results_text += f"Path found: {' -> '.join(path)}\n"
            results_text += f"Path length: {len(path)-1} edges\n"

            # total distance calculation
            total_distance = 0
            for i in range(len(path)-1):
                total_distance += self.edges[path[i]][path[i+1]]
            results_text += f"Total distance: {total_distance:.1f} meters\n\n"
        else:
            results_text += "No path found from {start} to {end}.\n\n"
        
        results_text += f"Traversal Order: {' -> '.join(visited)}"

        self.status_var.set(f"{self.current_algorithm} completed")
        self.show_results_window(results_text)
    
    def run_dijkstra(self):
        self.current_algorithm = "Dijkstra"
        start = self.start_path_var.get()
        end = self.end_path_var.get()
        
        if not start or not end:
            messagebox.showerror("Input Error", "Both start and end buildings must be selected.")
            return
        
        if start not in self.nodes or end not in self.nodes:
            messagebox.showerror("Input Error", "Selected buildings do not exist.")
            return

        # clear previous visualization
        self.visited_order = []
        self.path = []

        distances = {node: float('inf') for node in self.nodes}
        previous = {node: None for node in self.nodes}
        distances[start] = 0

        priority_queue = [(0, start)]
        visited = []

        while priority_queue:
            current_dist, current = heapq.heappop(priority_queue)
            if current in visited:
                continue

            visited.append(current)

            if current == end:
                break

            # explore neighbors
            for neighbor, distance in self.edges.get(current, {}).items():
                new_dist = current_dist + distance
                if new_dist < distances[neighbor]:
                    distances[neighbor] = new_dist
                    previous[neighbor] = current
                    heapq.heappush(priority_queue, (new_dist, neighbor))
        
        # reconstruct path
        path = []
        current = end
        while current is not None:
            path.append(current)
            current = previous[current]
        path.reverse()

        path_found = (distances[end] != float('inf'))
        self.visited_order = visited
        self.path = path if path_found else []
        self.draw_graph()

        # display results
        results_text = "Dijkstra's Algorithm Results:\n\n"
        if path_found:
            results_text += f"Shortest Path Found: {' -> '.join(path)}\n"
            results_text += f"Total Distance: {distances[end]:.1f} meters\n\n"
            results_text += f"Path Length: {len(path)-1} edges\n\n"
        else:
            results_text += "No path found from {start} to {end}.\n\n"

        results_text += f"Visited Order: {' -> '.join(visited)}"

        self.status_var.set("Dijkstra's Algorithm completed")
        self.show_results_window(results_text)

    def run_prim(self):
        self.current_algorithm = "Prim's MST"

        if len(self.nodes) < 2:
            messagebox.showerror("Input Error", "At least two buildings are required to compute MST.")
            return

        # clear previuous visualization (keep nodes still)
        self.visited_order = []
        self.path = []
        self.mst_edges = []

        visited = set()
        mst_edges = []
        total_weight = 0

        start_node = list(self.nodes.keys())[0]
        visited.add(start_node)

        # priority queue for edges
        edges_heap = []

        # initialize heap with edges from start node
        for neighbor, distance in self.edges.get(start_node, {}).items():
            heapq.heappush(edges_heap, (distance, start_node, neighbor))

        while edges_heap and len(visited) < len(self.nodes):
            weight, u, v = heapq.heappop(edges_heap)

            if v not in visited:
                visited.add(v)
                mst_edges.append((u, v, weight))
                total_weight += weight

                for neighbor, distance in self.edges.get(v, {}).items():
                    if neighbor not in visited:
                        heapq.heappush(edges_heap, (distance, v, neighbor))
            
        self.mst_edges = mst_edges
        self.draw_graph()

        # display results
        results_text = "Prim's Minimum Spanning Tree:\n\n"
        results_text += f"Total Weight: {total_weight:.1f} meters\n\n"
        results_text += f"Number of Edges: {len(mst_edges)}\n\n"
        results_text += f"Number of Buildings: {len(self.nodes)}\n\n"
        results_text += "Edges in MST:\n"

        for u, v, weight in mst_edges:
            results_text += f"{u} -- {v} : {weight:.0f} meters\n"
        
        self.status_var.set("Prim's MST completed")
        self.show_results_window(results_text)

# STUDY PLANNER MODULE #
class StudyPlanner:
    def __init__(self, parent_frame):
        self.frame = ttk.Frame(parent_frame)
        self.tasks = [] # list to store name, time, value tuples
        self.time_var = tk.StringVar()

        self.create_gui()

    def create_gui(self):
        # task input section...
        input_frame = ttk.LabelFrame(self.frame, text="Add Study Task")
        input_frame.pack(fill=tk.X, pady=(0, 10), padx=10)

        ttk.Label(input_frame, text="Task Name:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        self.task_name_var = tk.StringVar()
        ttk.Entry(input_frame, textvariable=self.task_name_var, width=20).grid(row=0, column=1, padx=5, pady=5)

        self.time_var = tk.StringVar()
        ttk.Label(input_frame, text="Time Required:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=5)
        ttk.Entry(input_frame, textvariable=self.time_var, width=10).grid(row=1, column=1, padx=5, pady=5)

        ttk.Label(input_frame, text="Value:").grid(row=1, column=2, sticky=tk.W, padx=5, pady=5)
        self.value_var = tk.StringVar()
        ttk.Entry(input_frame, textvariable=self.value_var, width=10).grid(row=1, column=3, padx=5, pady=5)
        
        ttk.Button(input_frame, text="Add Task", command=self.add_task).grid(row=2, column=0, columnspan=4, pady=10)

        # available time
        time_frame = ttk.LabelFrame(self.frame, text="Available Study Time")
        time_frame.pack(fill=tk.X, pady=(0, 10), padx=10)
        ttk.Label(time_frame, text="Total Available Time:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=5)
        
        self.available_time_var = tk.StringVar()
        ttk.Entry(time_frame, textvariable=self.available_time_var, width=15).grid(row=0, column=1, padx=5, pady=5)

        # algo buttons...
        algo_frame = ttk.Frame(time_frame)
        algo_frame.grid(row=1, column=0, columnspan=2, pady=10)

        ttk.Button(algo_frame, text="Greedy Scheduler", command=self.run_greedy).pack(side=tk.LEFT, padx=5)
        ttk.Button(algo_frame, text="Dynamic Programming Scheduler", command=self.run_dp).pack(side=tk.LEFT, padx=5)
        ttk.Button(algo_frame, text="Clear", command=self.clear_results).pack(side=tk.LEFT, padx=5)

        # task list
        list_frame = ttk.LabelFrame(self.frame, text="Study Tasks")
        list_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10), padx=10)

        # treeview for tasks...
        columns = ("Task Name", "Time Required", "Value")
        self.tasks_tree = ttk.Treeview(list_frame, columns=columns, show="headings", height=8)

        for c in columns: 
            self.tasks_tree.heading(c, text=c)
            self.tasks_tree.column(c, width=120)
        
        self.tasks_tree.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # display results
        results_frame = ttk.LabelFrame(self.frame, text="Results")
        results_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0,10))

        self.results_text = tk.Text(results_frame, height=12, wrap=tk.WORD)
        self.results_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.results_text.config(state=tk.DISABLED)

    def add_task(self):
        name = self.task_name_var.get().strip()
        time_str = self.time_var.get()
        value_str = self.value_var.get()

        if not name:
            messagebox.showerror("Input Error", "Task name cannot be empty.")
            return
        
        try:
            time = float(time_str)
            value = float(value_str)
            if time <= 0 or value <= 0:
                raise ValueError("Time and value must be positive.")
        except ValueError:
            messagebox.showerror("Input Error", "Time and value must be positive numbers.")
            return
        
        # add task to the list
        self.tasks.append((name, time, value))

        # update tasks display...
        self.update_tasks_display()

        # clear the input fields now
        self.task_name_var.set("")
        self.time_var.set("")
        self.value_var.set("")

    def update_tasks_display(self):
        # clear the display
        for item in self.tasks_tree.get_children():
            self.tasks_tree.delete(item)

        # add tasks...
        for name, time, value in self.tasks:
            self.tasks_tree.insert("", "end", values=(name, f"{time:.1f}", f"{value:.1f}"))
    
    def run_greedy(self):
        if not self.tasks:
            messagebox.showerror("Input Error", "No study tasks available.")
            return
        
        try:
            available_time = float(self.available_time_var.get())
            if available_time <= 0:
                raise ValueError("Available time must be positive.")
        except ValueError:
            messagebox.showerror("Input Error", "Available time must be a positive number.")
            return
        
        # greedy algorithm implementation (sort by value/time ratio)
        sorted_tasks = sorted(self.tasks, key=lambda x: x[2]/x[1], reverse=True)

        selected_tasks = []
        total_time = 0 # track total time used
        total_value = 0 # track total value gained

        for name, time, value in sorted_tasks:
            if total_time + time <= available_time: # check if we can add this task
                selected_tasks.append((name, time, value)) # add to selected
                total_time += time # update total time...
                total_value += value # update total value...
        
        # display results
        self.display_results("Greedy Scheduler", selected_tasks, total_time, total_value)
    
    def run_dp(self):
        if not self.tasks:
            messagebox.showerror("Input Error", "No study tasks available.")
            return

        try:
            available_time = float(self.available_time_var.get())
            if available_time <= 0:
                raise ValueError("Available time must be positive.")
        except ValueError:
            messagebox.showerror("Input Error", "Available time must be a positive number.")
            return
        
        # 0/1 knapsack dynamic programming approach
        n = len(self.tasks)
        W = int(available_time) # convert to int for dp table indexing

        # convert tasks to lists
        times = [int(task[1]) for task in self.tasks]
        values = [task[2] for task in self.tasks]
        names = [task[0] for task in self.tasks]

        # dp table...
        dp = [[0] * (W+1) for _ in range(n+1)]

        # fill the dp table
        for i in range(1, n+1):
            for w in range(1, W + 1):
                if times[i-1] <= w:
                    dp[i][w] = max(dp[i-1][w], values[i-1] + dp[i-1][w - times[i-1]])
                else:
                    dp[i][w] = dp[i-1][w]
        
        # backtrack to find selected tasks...
        selected_tasks = []
        total_time = 0
        total_value = dp[n][W]

        w = W
        for i in range(n, 0, -1):
            if dp[i][w] != dp[i-1][w]:
                selected_tasks.append(self.tasks[i-1])
                total_time += times[i-1]
                w -= times[i-1]

        selected_tasks.reverse() # maintain original order

        # display results
        self.display_results("Dynamic Programming Scheduler", selected_tasks, total_time, total_value)

    def display_results(self, algorithm_name, selected_tasks, total_time, total_value):
        self.results_text.config(state=tk.NORMAL)
        self.results_text.delete(1.0, tk.END)

        self.results_text.insert(tk.END, f"=== {algorithm_name} ===\n\n")

        self.results_text.insert(tk.END, "Selected Study Tasks:\n")
        for name, time, value in selected_tasks:
            self.results_text.insert(tk.END, f"- {name} (Time: {time}, Value: {value})\n")

        self.results_text.insert(tk.END, f"\nTime total: {total_time:.1f}\n")
        self.results_text.insert(tk.END, f"Value total: {total_value:.1f}\n")

        self.results_text.config(state=tk.DISABLED)
    
    def clear_results(self):
        self.results_text.config(state=tk.NORMAL)
        self.results_text.delete(1.0, tk.END)
        self.results_text.config(state=tk.DISABLED)

# NOTES SEARCH ENGINE MODULE #
class NotesSearchEngine:
    def __init__(self, parent_frame):
        self.frame = ttk.Frame(parent_frame)
        self.current_text = "" # store the text of the loaded document
        self.search_results = {} # store results from different algos

        self.create_gui()

    def create_gui(self):
        # upload file section...
        file_frame = ttk.LabelFrame(self.frame, text="📁 Upload Document")
        file_frame.pack(fill=tk.X, pady=(0, 10), padx=10)

        ttk.Button(file_frame, text="Upload Document", command=self.upload_document).pack(fill=tk.X, pady=5)

        self.file_status_var = tk.StringVar(value="No document uploaded.")
        ttk.Label(file_frame, textvariable=self.file_status_var).pack(pady=5)

        # Document display box
        doc_display_frame = ttk.LabelFrame(self.frame, text="Document Content")
        doc_display_frame.pack(fill=tk.BOTH, expand=True, pady=(0,10), padx=10)

        self.doc_text = tk.Text(doc_display_frame, height=15, wrap=tk.WORD)
        doc_scrollbar = ttk.Scrollbar(doc_display_frame, orient=tk.VERTICAL, command = self.doc_text.yview)
        self.doc_text.config(yscrollcommand=doc_scrollbar.set)
        self.doc_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5,0), pady=5)
        doc_scrollbar.pack(side=tk.RIGHT, fill=tk.Y, padx=(0,5), pady=5)
        self.doc_text.config(state=tk.DISABLED)

        # search section...
        search_frame = ttk.LabelFrame(self.frame, text="Search Notes")
        search_frame.pack(fill=tk.X, pady=(0,10),padx=10)

        ttk.Label(search_frame, text="Search Pattern:").pack(anchor=tk.W)
        self.pattern_var = tk.StringVar()
        ttk.Entry(search_frame, textvariable=self.pattern_var, width=50).pack(fill=tk.X, pady=(0,5))

        # algo buttons
        algo_frame = ttk.Frame(search_frame)
        algo_frame.pack(fill=tk.X, pady=5)

        self.algo_var = tk.StringVar(value="Naive")
        ttk.Radiobutton(algo_frame, text="Naive", variable = self.algo_var, value="Naive").pack(side=tk.LEFT)
        ttk.Radiobutton(algo_frame, text="Rabin-Karp", variable=self.algo_var, value="Rabin-Karp").pack(side=tk.LEFT)
        ttk.Radiobutton(algo_frame, text="KMP", variable=self.algo_var, value="KMP").pack(side=tk.LEFT)
        ttk.Radiobutton(algo_frame, text="ALL (Compare)", variable=self.algo_var, value="ALL").pack(side=tk.LEFT)
        ttk.Button(search_frame, text="Search", command=self.run_search).pack(fill=tk.X, pady=5)

        # results display
        results_frame = ttk.LabelFrame(self.frame, text="Search Results")
        results_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0,10))

        # text widget for results...
        self.results_text = tk.Text(results_frame, height=20, wrap=tk.WORD)
        scrollbar = ttk.Scrollbar(results_frame, orient=tk.VERTICAL, command=self.results_text.yview)

        self.results_text.config(yscrollcommand=scrollbar.set)

        self.results_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5,0), pady=5)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y, padx=(0,5), pady=5)
        self.results_text.config(state=tk.DISABLED)

    def upload_document(self):
        file_path = filedialog.askopenfilename(
            title="Select Document",
            filetypes=[("All supported", "*.pdf *.docx *.txt"), ("PDF files", "*.pdf"), ("Word Documents", "*.docx"), ("Text files", "*.txt")]
        )

        if not file_path:
            return

        try:
            if file_path.endswith('.pdf'): # if pdf...
                text = self.extract_text_from_pdf(file_path)
            elif file_path.endswith('.docx'): # if word doc
                text = self.extract_text_from_docx(file_path)
            elif file_path.endswith('.txt'): # if text file
                text = self.extract_text_from_txt(file_path)
            else:
                messagebox.showerror("File Error", "Unsupported file format.")
                return
            
            self.current_text = text
            self.file_status_var.set(f"Loaded: {file_path.split('/')[-1]} ({len(text)} characters)")

            # display the document in text box.
            self.doc_text.config(state=tk.NORMAL)
            self.doc_text.delete(1.0, tk.END)
            self.doc_text.insert(1.0, text)
            self.doc_text.config(state=tk.DISABLED)
        
        except Exception as e:
            messagebox.showerror("File Error", f"Failed to load document: {str(e)}")
        
    def extract_text_from_pdf(self, file_path):
        text = ""
        with open(file_path, 'rb') as file:
            reader = PyPDF2.PdfReader(file)
            for page in reader.pages:
                text += page.extract_text() + "\n"
        return text

    def extract_text_from_docx(self, file_path):
        doc = docx.Document(file_path)
        text = ""
        for paragraph in doc.paragraphs:
            text += paragraph.text + "\n"

        return text

    def extract_text_from_txt(self, file_path):
        with open(file_path, 'r', encoding='utf-8') as file:
            text = file.read()
        return text
    
    def run_search(self):
        if not self.current_text:
            messagebox.showerror("Input Error", "No document loaded for searching.")
            return
        
        pattern = self.pattern_var.get().strip()
        if not pattern:
            messagebox.showerror("Input Error", "Search pattern cannot be empty.")
            return

        selected_algo = self.algo_var.get()

        # clear any previous results...
        self.search_results = {}

        if selected_algo == "ALL":
            # run all algos and compare them against each other
            algorithms = [
                ("Naive", self.naive_search),
                ("Rabin-Karp", self.rabin_karp_search),
                ("KMP", self.kmp_search)
            ]
            for name, algorithm in algorithms:
                start_time = time.time()
                indices = algorithm(self.current_text, pattern)
                end_time = time.time()
                self.search_results[name] = {
                    'indices': indices,
                    'time': end_time - start_time,
                    'matches': len(indices)
                }
        else:
            # run the selected algo
            if selected_algo == "Naive":
                algorithm = self.naive_search
            elif selected_algo == "Rabin-Karp":
                algorithm = self.rabin_karp_search
            elif selected_algo == "KMP":
                algorithm = self.kmp_search
            
            start_time = time.time()
            indices = algorithm(self.current_text, pattern)
            end_time = time.time()

            self.search_results[selected_algo] = {
                'indices': indices,
                'time': end_time - start_time,
                'matches': len(indices)
            }

        self.display_results(pattern)

    def naive_search(self,text,pattern):
        indices = []
        n = len(text)
        m = len(pattern)

        for i in range(n - m +1):
            if text[i:i+m] == pattern:
                indices.append(i)
        return indices

    def rabin_karp_search(self,text,pattern):
        indices = []
        n = len(text)
        m = len(pattern)
        # if pattern is empty or longer than the text, just return empty.
        if m == 0 or n < m:
            return indices
        
        # prime number for hashing
        prime = 101
        d = 256 # number of characters in ASCII alphabet

        # calculate hash values
        pattern_hash = 0
        text_hash = 0
        h = 1
        
        for i in range(m-1):
            h = (h*d) % prime
        
        # initial hash values...
        for i in range(m):
            pattern_hash = (d * pattern_hash + ord(pattern[i])) % prime
            text_hash = (d * text_hash + ord(text[i])) % prime

        # slide pattern over text
        for i in range(n - m +1):
            if pattern_hash == text_hash:
                # if the hash matches, check the characters to avoid false positives...
                if text[i:i + m] == pattern:
                    indices.append(i)
            # hash for next window is calculated... (rolling)
            if i < n - m:
                text_hash = (d * (text_hash - ord(text[i]) * h) + ord(text[i+m])) % prime
                # fix if negative.
                if text_hash < 0:
                    text_hash += prime
        return indices
    
    def kmp_search(self, text, pattern):
        indices = []
        n = len(text)
        m = len(pattern)

        if m == 0:
            return indices

        # preprocess the pattern
        lps = [0] * m # longest prefix suffix
        length = 0 
        i = 1

        while i < m:
            if pattern[i] == pattern[length]:
                length += 1
                lps[i] = length
                i += 1
            else:
                if length != 0:
                    length = lps[length - 1]
                else:
                    lps[i] = 0
                    i += 1
        
        # search via lps array
        i = 0 # pattern index
        j = 0 # text index

        while i < n:
            if pattern[j] == text[i]:
                i += 1
                j += 1
            
            if j == m:
                indices.append(i-j)
                j = lps[j-1]
            elif i < n and pattern[j] != text[i]:
                if j != 0:
                    j = lps[j-1]
                else:
                    i += 1

        return indices

    def display_results(self, pattern):
        self.results_text.config(state=tk.NORMAL)
        self.results_text.delete(1.0, tk.END)

        if not self.search_results:
            self.results_text.insert(tk.END, "No results found.")
            self.results_text.config(state=tk.DISABLED)
            return

        for algo_name, result in self.search_results.items():
            self.results_text.insert(tk.END, f"=== {algo_name} Algorithm ===\n")
            self.results_text.insert(tk.END, f"Pattern: '{pattern}'\n")
            self.results_text.insert(tk.END, f"Matches found: {result['matches']}\n")
            self.results_text.insert(tk.END, f"Time taken: {result['time']:.6f} seconds\n")

            if result['indices']:
                self.results_text.insert(tk.END, f"Match positions: {result['indices'][:20]}") # show first 20 
                if len(result['indices']) > 20:
                    self.results_text.insert(tk.END, f" ... and {len(result['indices']) - 20} more")
                self.results_text.insert(tk.END, "\n")
            else:
                self.results_text.insert(tk.END, "No matches found.\n")
            
            self.results_text.insert(tk.END, "\n")

        # if all algos were chosen to be run
        if len(self.search_results) > 1:
            self.results_text.insert(tk.END, "=== PERFORMANCE COMPARISON ===\n")
            fastest_algo = min(self.search_results.items(), key=lambda x: x[1]['time']) # show the fastest algo.
            self.results_text.insert(tk.END, f"Fastest algorithm: {fastest_algo[0]} ({fastest_algo[1]['time']:.6f}s)\n")
        self.results_text.config(state=tk.DISABLED)    

# Algorithm Info Module (last module)#
class AlgorithmInfo:
    def __init__(self,parent_frame):
        self.frame = ttk.Frame(parent_frame)
        self.frame.pack(fill=tk.BOTH, expand=True)
        self.create_gui()

    def create_gui(self):
        self.frame.configure(style="TFrame")
        title_label = tk.Label(
            self.frame,
            text="Algorithm Information",
            font=("Georgia", 24, "bold"),
            bg = '#f0f8ff',
            fg = '#2c3e50'
        )
        title_label.pack(pady=(20,30))

        text_frame = ttk.Frame(self.frame)
        text_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=(0,20))

        self.text_widget = tk.Text(
            text_frame,
            wrap=tk.WORD,
            font=("Georgia", 11),
            bg = '#ffffff',
            relief=tk.FLAT,
            borderwidth=2,
            padx=15,
            pady=15
        )

        # create a scrollbar...
        scrollbar = ttk.Scrollbar(text_frame, orient=tk.VERTICAL, command=self.text_widget.yview)
        self.text_widget.configure(yscrollcommand=scrollbar.set)

        self.text_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.text_widget.tag_configure("bold", font=("Georgia", 12, "bold"))
        self.text_widget.insert(tk.END, "This is an interactive Python application that combines multiple algorithmic modules together. Below are the Big-O complexities of each algorithm.\n\n", "bold")
        algorithm_info = """ 1. BFS (Breadth-First Search): A graph traversal algorithm that explores all neighboring nodes at the current depth prior to progressing to nodes at the next depth level. 
        It guarantees that the shortest path is found within a graph. 
                - Time Complexity: 
                        • Average-case: O(V + E), where "V" is the number of vertices and "E" is the number of edges. BFS contains an array that tracks each vertex and edge, making 
                                        sure that each is processed only once. 
                        • Worst-case: O(V + E)
                        • Best-case: O(V + E)
        
        2. Dijkstra's Algorithm: Used for graphs with varying weighted edges (no negative edges) in which a priority queue is used to always expand the most promising node 
                                 first. A distance array is also maintained in order to keep track of the minimum distance found so far. It also prevents the unnecessary 
                                 revisiting of nodes, thus enhancing the algorithm's efficiency overall.
                - Time Complexity: 
                        • Average-case: O((V+E)*logV), where "E" is the number of edges and "V" is the number of vertices. Each vertex is extracted from the priority queue only once, 
                                        and each edge is only examined once.
                        • Worst-case: O((V+E)*logV)
                        • Best-case: O((V+E)*logV)
        
        3. DFS (Depth-First Search): A graph traversal method that starts at a source vertex and explores each path completely until it reaches a vertex with no unvisited neighbors.
                                    Then, it backtracks to examine other unvisited paths, ensuring that all vertices that can be reached from the source node are explored. DFS is unique
                                    due to the fact that it holds an extra visited array in order to account for loops within the graph - making sure that a vertex is not processed 
                                    more than once.
                - Time Complexity: 
                        • Average-case: O(V+E), where "V" is the number of vertices and "E" is the number of edges. This is linear as DFS visits each vertex and each edge in the worst-case
                                        scenario, regardless.
                        • Worst-case: O(V+E)
                        • Best-case: O(V+E)
        
        4. Prim's MST: A greedy algorithm that adds edges with the minimum edge weight one at a time, gradually building a minimum spanning tree. 
                - Time Complexity: 
                        • Average-case: O(E log V), where "E" is the number of edges and "V" is the number of vertices. This is because every edge is considered once and can be added to the 
                                        priority queue, with each priority queue operation taking O(log V) time. 
                        • Worst-case: O(E log V)
                        • Best-case: O(E log V)

        5. Greedy Algorithm: Select the best looking (or locally optimal) choice at each step with the goal of reaching a globally optimal - or best overall - solution. In regards to the 
                            study scheduler module, the greedy approach continuously selects each task with the smallest value/time ratio. 
                - Time Complexity: 
                        • Average-case: O(n log n), where "n" is the input size. This is due to the fact that most greedy algorithms utilize a priority queue, in which each push/pop is O(log n).
                                        However, the greedy algorithm must do this "n" times, meaning that the final complexity will be O(n * log n).
                        • Worst-case: O(n log n)
                        • Best-case: O(n log n)

        6. Dynamic Programming (Knapsack): Used in a scenario where there are n distinct items and a total weight capacity of W. Each item has a weight (w) and value (v) associated with it. 
                                           A DP table is created in which the row represents the item and the columns represent the weight capacity. Each cell holds the maximum value 
                                           achievable. Thus, the main idea is to maximize the value whilst staying within the limited weight capacity. In every iteration, DP considers whether
                                           to include/exclude a particular item based on if it would have a higher value and stay within the weight limitation. Thus, it is considering multiple
                                           combinations at each step.
                - Time Complexity: 
                        • Average-case: O(n * W), where "n" is the input size and "W" is the weight capacity. This is because the DP table has n rows and W columns (one for each weight capacity), 
                                        meaning that the total amount of iterations performed throughout the table is n * W.  
                        • Worst-case: O(n * W)
                        • Best-case: O(n * W)

        7. Naive Search: The simplest string-matching algorithm that checks for the pattern over the given text character by character, repeatedly checking for a match. This is repeated until the 
                         end of the text has been reached. 
                - Time Complexity (DIFFERING COMPLEXITIES): 
                        • Average-case: O(n + m), where "n" is the length of the text and "m" is the length of the pattern. Since mismatches usually occur early, very few characters are checked each time 
                                        meaning that the algorithm behaves linearly.
                        • Worst-case: O((n-m+1)*m); This occurs when all characters in both the text (n) and the pattern (m) are the same except for the very last character, which causes the algorithm to 
                                      repeatedly compare the matching characters for every iteration. 
                        • Best-case: O(n); This occurs if the pattern does not have any characters that match the text. This means that the each character fails immediately with only 1 comparison per 
                                    window.

        8. Rabin-Karp: This algorithm converts the strings into a numeric fingerprint (or hash) and compares the hashes against each other. If the hashes between the text and the pattern differ, 
                       then the algorithm quickly skips it. If the hashes do match, then real character comparisons are performed. To go into further detail, a rolling hash is used in which the 
                       hash of the pattern is computed and then the hashes of all substrings (or words) within a text are computed for comparison. If the hashes between the pattern and substring 
                       matches, then real character comparison is performed to double-check and avoid hash collisions.
                - Time Complexity (DIFFERING COMPLEXITIES): 
                        • Average-case: Θ(n + m) ≈ Θ(n); This occurs when collisions are rare and the algorithm behaves in linear time.
                        • Worst-case: O(n * m); The worst case occurs when there are many hash collisions, which lead to full character comparisons being performed. 
                        • Best-case: O(n), where "n" represents the input size. Since the hashes of the pattern and substrings are "precomputed", it takes linear time to pass through the string and
                                   find any matches. The best case is when no hash collisions occur.

        9. KMP (Knuth-Morris-Pratt): This algorithm preprocesses the pattern by building an array known as LPS (Longest Prefix Suffix). Essentially, the algorithm is avoiding redundant comparisons 
                                    by storing the length of the longest prefix that has been found. If a mismatch occurs, the algorithm simply skips over the longest prefix and continues trying to 
                                    find a viable match. So instead of starting over, the algorithm is able to "remember" whether the text already includes some of the pattern and prevents itself from
                                    rechecking matched characters. This is great for repetitive patterns. Also, there is no hashing used within this algorithm, meaning that it is not susceptible to collisions.
                - Time Complexity: 
                        • Average-case: O(n+m), where "n" represents the length of the text and "m" represents the length of the pattern. This is because building the LPS array takes O(m) time while 
                                searching for the pattern within the text takes O(n) time, since the text is only scanned once. 
                        • Worst-case: O(n+m)
                        • Best-case: O(n+m)
         """
        
        self.text_widget.insert(tk.END, algorithm_info)
        self.text_widget.config(state=tk.DISABLED)
        pnp_frame = ttk.Frame(self.frame)
        pnp_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=(0,20))

        self.pnp_text = tk.Text(
            pnp_frame,
            wrap=tk.WORD,
            font=("Georgia", 11),
            bg = '#ffffff',
            relief=tk.FLAT,
            borderwidth=2,
            padx=15,
            pady=15,
            height=12
        )

        pnp_scroll = ttk.Scrollbar(pnp_frame, orient=tk.VERTICAL, command=self.pnp_text.yview)
        self.pnp_text.configure(yscrollcommand=pnp_scroll.set)

        self.pnp_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        pnp_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.pnp_text.tag_configure("bold", font=("Georgia", 12, "bold"))
        self.pnp_text.insert(tk.END, "P vs NP Hard:\n\n", "bold")

        pnp_info = (
            """A polynomial-time (P) problem is considered efficient if it finishes in a reasonable amount of time as the input size grows. In contrast, Non-Deterministic Polynomial (NP) problems are easy to verify but difficult to solve. NP-hard problems cannot be solved in polynomial time, and the objective is often to find a survivable or “good enough” solution rather than a perfect one.
            To determine whether a problem is NP-hard, we use reduction, which acts like a proof by contradiction. If you suspect that Problem A is NP-hard, you compare it to a well-known NP-hard problem that can be referred to as Problem B. If Problem B can be readily reduced to Problem A, then Problem A is NP-hard since it contains the same level of difficulty as Problem B. Thus, 
            reduction and logical reasoning can be used to prove that a problem is NP-hard.
            An example of an NP-hard problem is the 0/1 Knapsack problem discussed in the Study Planner Module. This problem is NP-hard because finding an optimal solution is difficult, but verifying a solution is quite easy. 
            By creating both the Greedy Scheduler and DP method for the Study Planner module, I experienced firsthand why the 0/1 Knapsack problem is classified as NP-hard. Although checking to see if a set of tasks can be completed within the time constraint is very quick, determining the best possible combination becomes increasingly difficult as the number of tasks rises. The 
            pseudo-polynomial time complexity within the DP algorithm demonstrated to me how fast the computation can become costly when the available time (W) increases. This illustrates the significance of NP-hard problems in practical computing, since we simply do not have the resources to always compute the "perfect" solution. Therefore, programmers turn to heuristics - like 
            the greedy approach - to arrive at "good enough" answers within a reasonable time frame. This trade-off between finding optimal solutions and receiving solutions within a quick time frame lies at the core of P vs NP, which I understood while completing this project.
            """
        )

        self.pnp_text.insert(tk.END, pnp_info)
        self.pnp_text.config(state=tk.DISABLED)
        
class allModules:
    def __init__(self, root):
        self.root = root
        self.root.title("Titan Campus Algorithmic Assistant")
        self.root.geometry("1400x900")

        # configuring light blue for style of app
        style=ttk.Style()
        style.configure("TFrame", background='#f0f8ff') # color is light blue
        style.configure("TNotebook", background='#f0f8ff')
        style.configure("TNotebook.Tab", background='#f0f8ff')
        style.configure("TLabelframe", background = '#f0f8ff')
        style.configure("TLabel", background='#f0f8ff')
        style.configure("TButton", background='#f0f8ff')

        # configure root background
        self.root.configure(bg='#f0f8ff')

        # create the notebook for tabs
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        # create frames for each module...
        self.campus_frame = ttk.Frame(self.notebook)
        self.study_frame = ttk.Frame(self.notebook)
        self.notes_frame = ttk.Frame(self.notebook)
        self.info_frame = ttk.Frame(self.notebook)

        # add the tabs accordingly.
        self.notebook.add(self.campus_frame, text="Campus Navigation System")
        self.notebook.add(self.study_frame, text="Study Planner")
        self.notebook.add(self.notes_frame, text="Notes Organizer")
        self.notebook.add(self.info_frame, text="Algorithm Info")

        # initialize the modules accordingly.
        self.campus_module = CampusNavigationSystem(self.campus_frame)
        self.study_module = StudyPlanner(self.study_frame)
        self.notes_module = NotesSearchEngine(self.notes_frame)
        self.info_module = AlgorithmInfo(self.info_frame)

        # pack the modules...
        #self.campus_module.pack(fill=tk.BOTH, expand=True)
        self.study_module.frame.pack(fill=tk.BOTH, expand=True)
        self.notes_module.frame.pack(fill=tk.BOTH, expand=True)
        self.info_module.frame.pack(fill=tk.BOTH, expand=True)

def main():
    root = tk.Tk()
    app = allModules(root)
    root.mainloop()

if __name__ == "__main__":
    main()