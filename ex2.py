import random
import math
# import json
import itertools
import time
import ast
import numpy as np
from collections import deque
import copy
import networkx as nx
import additional_inputs

ids = ["316350651", "324620814"]

def product_dict(dic):
    keys = dic.keys()
    vals = dic.values()
    for instance in itertools.product(*vals):
        yield dict(zip(keys, instance))

class OptimalTaxiAgent:

    def new_distance_matrix(self,graph):
        distance_matrix_fw = self.floyd_warshall(graph)
        return distance_matrix_fw

    def create_graph(self, map):
        graph = {}
        for i in range(len(map)):
            for j in range(len(map[0])):
                graph[(i, j)] = {}
                if map[i][j] != 'I':
                    if i > 0 and map[i - 1][j] != 'I':
                        graph[(i, j)][(i - 1, j)] = 1
                    if i < len(map) - 1 and map[i + 1][j] != 'I':
                        graph[(i, j)][(i + 1, j)] = 1
                    if j > 0 and map[i][j - 1] != 'I':
                        graph[(i, j)][(i, j - 1)] = 1
                    if j < len(map[0]) - 1 and map[i][j + 1] != 'I':
                        graph[(i, j)][(i, j + 1)] = 1
        return graph

    # apply floyd warshall algorithm to the graph
    def floyd_warshall(self, graph):
        distance_matrix = {}
        for i in graph.keys():
            distance_matrix[i] = {}
            for j in graph.keys():
                if i == j:
                    distance_matrix[i][j] = 0
                elif j in graph[i].keys():
                    distance_matrix[i][j] = graph[i][j]
                else:
                    distance_matrix[i][j] = math.inf
        for k in graph.keys():
            for i in graph.keys():
                for j in graph.keys():
                    distance_matrix[i][j] = min(distance_matrix[i][j], distance_matrix[i][k] + distance_matrix[k][j])
        return distance_matrix


    def all_taxi_possible_locations(self):
        #make a list of all locations in the map that are not 'I'
        all_locations = []
        for i in range(len(self.map)):
            for j in range(len(self.map[0])):
                if self.map[i][j] != 'I':
                    all_locations.append((i,j))
        return all_locations


    def get_all_passenger_locations_unpicked_old(self):
        all_unpicked_passenger_locations = {}
        for passenger in self.initial["passengers"].keys():
            dest = self.destinations_by_passenger[passenger]
            if len(dest) == 1:
                dest = dest,
            loc = self.initial["passengers"][passenger]["location"]
            if loc not in dest:
                all_unpicked_passenger_locations[passenger] = dest + (loc,)
            else:
                all_unpicked_passenger_locations[passenger] = dest
        return all_unpicked_passenger_locations


    def get_all_passenger_locations_unpicked(self):
        all_unpicked_passenger_locations = {}
        for passenger in self.initial["passengers"].keys():
            dest = self.destinations_by_passenger[passenger]
            dest = list(dest)
            loc = self.initial["passengers"][passenger]["location"]
            if loc not in dest:
                #make the outcome a tuple of (dest1, dest2, ... ,loc)
                outcome = dest + [loc]
                all_unpicked_passenger_locations[passenger] = tuple(outcome)
            else:
                all_unpicked_passenger_locations[passenger] = dest
        return all_unpicked_passenger_locations


    def get_all_possible_raw_states(self):
        locations_list = itertools.permutations(self.all_taxi_possible_locations(), len(self.initial["taxies"]))
        current_passengers_list = []
        current_passengers_in_each_car_possibilities = []
        for taxi_name in self.initial["taxies"].keys():
            #    len_gas = self.max_fuel_dict[taxi_name]+1
            #    fuels_list.append([*range(len_gas)])
            len_passengers = len(self.initial["passengers"])+1
            current_passengers_list.append([*range(len_passengers)])
        current_passengers_in_each_car_possibilities = list(itertools.product(*current_passengers_list))
        max_passengers = len(self.initial["passengers"].keys())
        current_passengers_in_each_car_possibilities = [item for item in current_passengers_in_each_car_possibilities
                                                        if sum(item) <= max_passengers]

        state = {"taxies": {}, "passengers": {}}
        for taxi_name in self.initial["taxies"].keys():
            state["taxies"][taxi_name] = {'location': None, 'curr_passengers': None, 'curr_fuel': None}
        for passenger_name in self.initial["passengers"].keys():
            state["passengers"][passenger_name] = {'location': None, 'destination': None}

        for location in locations_list: #location is (loc1,loc2,loc3)
            for taxi_location,taxi_name_for_loc in zip(location,self.taxies): #taxi_location is loc1, taxi_name_for_loc is taxi1
                state["taxies"][taxi_name_for_loc]["location"] = taxi_location
            fuels_list_by_state = []

            for taxi_name in self.initial["taxies"].keys():
                loc_of_taxi = state["taxies"][taxi_name]["location"]
                len_gas = self.max_fuel_dict_by_location[(loc_of_taxi, taxi_name)] + 1
                fuels_list_by_state.append([*range(len_gas)])
            fuels_list_by_state = list(itertools.product(*fuels_list_by_state))


            for fuel_of_taxis in fuels_list_by_state: #fuel_of_taxis is (fuel1,fuel2,fuel3)
                if len(fuel_of_taxis) == 1:
                    fuel_of_taxis = fuel_of_taxis,
                for fuel_of_taxi, taxi_name_for_fuel in zip(fuel_of_taxis,self.taxies):
                    if type(fuel_of_taxi) == tuple:
                        fuel_of_taxi = fuel_of_taxi[0]
                    state["taxies"][taxi_name_for_fuel]["curr_fuel"] = fuel_of_taxi
                for current_passengers_in_taxies in current_passengers_in_each_car_possibilities: #item is (1,2,3)
                    for passengers_in_taxi,taxi_name_for_curr_passengers in zip(current_passengers_in_taxies,self.taxies):
                        state["taxies"][taxi_name_for_curr_passengers]["curr_passengers"] = passengers_in_taxi
                    self.all_placements = []
                    self.find_all_combinations_of_vectors(current_passengers_in_taxies, self.passengers, [])
                    self.all_placements = [ast.literal_eval(item) for item in self.all_placements]
                    for placement in self.all_placements:
                        for passengers_in_taxi,taxi_name_for_names_of_passengers in zip(placement,self.taxies):
                            for passenger_in_taxi in passengers_in_taxi:
                                state["passengers"][passenger_in_taxi]["location"] = taxi_name_for_names_of_passengers
                        picked_up_passengers = sum(placement,())
                        unpicked_up_passengers = [p for p in self.passengers if p not in picked_up_passengers]
                        unpicked_dict = { your_key: self.legal_passenger_locations[your_key] for your_key in unpicked_up_passengers }
                        for passengers_and_locations in product_dict(unpicked_dict):
                            for passenger_unpicked,passenger_location in passengers_and_locations.items():
                                state["passengers"][passenger_unpicked]["location"] = passenger_location
                            for passengers_and_destinations in product_dict(self.destinations_by_passenger):
                                for passenger_for_destination,destination in passengers_and_destinations.items():
                                    state["passengers"][passenger_for_destination]["destination"] = destination
                                state_as_str = str(state)
                                self.all_possible_raw_states.append(str(state))
                                actions = self.actions(state_as_str)
                                self.all_actions_by_raw_state[state_as_str] = actions
                                for action in actions:
                                    self.all_results_and_probs_by_raw_state_action[(state_as_str,action)] = self.result(state_as_str,action)

    def check_if_list_unique(self, list):
        if len(list) == len(set(list)):
            return True
        else:
            return False


    def find_all_combinations_of_vectors(self, vector, unseated_passengers, placement):
        if vector == ():
            self.all_placements.append(str(placement))
            return
        list_of_optional_subset = itertools.combinations(unseated_passengers, vector[0])
        for subset in list_of_optional_subset:
            placement.append(subset)
            unseated_passengers = [item for item in unseated_passengers if item not in subset]
            self.find_all_combinations_of_vectors(vector[1:], unseated_passengers, placement)
            unseated_passengers = unseated_passengers + list(subset)
            placement.pop()


    def get_all_actions_by_raw_state(self): ##state is a string
        for state in self.all_possible_raw_states:
            self.all_actions_by_raw_state[state] = self.actions(state)
        return


    def get_all_results_and_probs_by_raw_state_action(self): ##state is a string
        for state in self.all_possible_raw_states:
            for action in self.all_actions_by_raw_state[state]:
                self.all_results_and_probs_by_raw_state_action[(state, action)] = self.result(state, action)


    def get_max_fuel_dict_by_location(self):
        core_locations = {}
        for taxi_name in self.taxies:
            core_locations[taxi_name] = [self.initial["taxies"][taxi_name]["location"]] + self.gas_stations
        #this is a dict where the keys are tuples of (location,taxi) and the values are the max fuel for that taxi at that location
        #the max fuel is the max fuel of that taxi, minus the distance from that location to one of the core_locations
        #go over all the possible locations and find the max fuel for each taxi at that location
        for location in self.legal_taxi_locations:
            for taxi_name in self.taxies:
                max_fuel = self.initial["taxies"][taxi_name]["curr_fuel"]
                g = []
                for core_location in core_locations[taxi_name]:
                    g.append(max_fuel - self.distance_matrix_fw[location][core_location])
                self.max_fuel_dict_by_location[(location,taxi_name)] = max(g)


    def get_all_possible_states(self):
        turns_to_go = self.N
        all_possible_states = set(([(str(self.initial), turns_to_go)]))
        set_of_states_current_level = set(([(str(self.initial), turns_to_go)]))
        turns_to_go -= 1
        #put the (state,turns_to_go) in the set as a tuple
        while set_of_states_current_level and turns_to_go > 0:
            set_of_states_next_level = set()
            for state in set_of_states_current_level:
                raw_state = state[0]
                for action in self.all_actions_by_raw_state[raw_state]:
                    results = self.all_results_and_probs_by_raw_state_action[raw_state, action] #results is a list of tuples (prob,result)
                    for result in results:
                        set_of_states_next_level.add((result[1], turns_to_go))
            all_possible_states = all_possible_states.union(set_of_states_next_level)
            set_of_states_current_level = set_of_states_next_level
            turns_to_go -= 1
        #sort all_possible_states by turns_to_go, from largest to smallest
        all_possible_states = sorted(all_possible_states, key=lambda x: x[1])
        state_indices = [state[1] for state in all_possible_states]
        self.all_possible_states = all_possible_states


    def __init__(self, initial, for_optimal_policy=True):
        self.N = initial["turns to go"]
        self.map = initial["map"]
        self.all_placements = []
        state = {}
        state["taxies"] = {}
        state["passengers"] = {}
        # create a capacity dict for each taxi
        self.capacity_dict = {}
        # create a max fuel dict for each taxi
        self.max_fuel_dict = {}
        # fill the data accordingly
        for taxi in initial["taxis"].keys():
            taxi_info = initial["taxis"][taxi]
            state["taxies"][taxi] = {"location": taxi_info["location"],
                                     "curr_passengers": 0,
                                     "curr_fuel": taxi_info["fuel"],
                                     }
            self.max_fuel_dict[taxi] = taxi_info["fuel"]
            self.capacity_dict[taxi] = taxi_info["capacity"]

        # create a dict of all possible destinations for each passenger
        self.destinations_by_passenger = {}
        # create a dict of all probabilities for each passenger
        self.probabilities_by_passenger = {}
        # fill the data accordingly
        for passenger in initial["passengers"].keys():
            passenger_info = initial["passengers"][passenger]
            state["passengers"][passenger] = {"location": passenger_info["location"],
                                              "destination": passenger_info["destination"],
                                              }
            self.destinations_by_passenger[passenger] = passenger_info["possible_goals"]
            p = passenger_info["prob_change_goal"]
            k = len(passenger_info["possible_goals"])
            self.probabilities_by_passenger[passenger] = {}
            self.probabilities_by_passenger[passenger][True] = 1-p*(1-1/k)
            #TRUE MEANS THAT THE PASSENGER DID NOT CHANGE DESTINATION
            #CURRENT_DEST == FUTURE_DEST
            if k != 1:
                stay_prob = self.probabilities_by_passenger[passenger][True]
                self.probabilities_by_passenger[passenger][False] = (1-stay_prob)/(k-1)
            else:
                self.probabilities_by_passenger[passenger][True] = 1
                self.probabilities_by_passenger[passenger][False] = 0


        #make a list of gas stations
        # in self.map, find all gas stations and add them to self.gas_stations
        self.gas_stations = []
        for i in range(len(self.map)):
            for j in range(len(self.map[0])):
                if self.map[i][j] == "G":
                    self.gas_stations.append((i, j))

        self.reward_dict = {"drop off": 100,
                            "r": -50,
                            "refuel": -10,
                            "move": 0,
                            "pick up": 0,
                            "wait": 0,
                            }

        self.discount_factor = 1

        self.operations = {"move left": 1,
                           "move right": 1,
                           "move up": 1,
                           "move down": 1,
                           "pick up": 1,
                           "drop off": 1,
                           "refuel": 1,
                           "wait": 1}
        self.graph = self.create_graph(self.map)
        self.distance_matrix_fw = self.new_distance_matrix(self.graph)
        self.initial = state
        self.legal_taxi_locations = self.all_taxi_possible_locations()
        self.legal_passenger_locations = self.get_all_passenger_locations_unpicked()
        self.passengers = initial["passengers"].keys()
        self.taxies = initial["taxis"].keys()
        self.max_fuel_dict_by_location = {}
        self.get_max_fuel_dict_by_location()
        self.all_possible_raw_states = []
        self.all_actions_by_raw_state = {}
        self.all_results_and_probs_by_raw_state_action = {}
        self.get_all_possible_raw_states()
        # print("all possible raw states length: ", len(self.all_possible_raw_states))
        if for_optimal_policy:
            self.all_possible_states = []
            self.get_all_possible_states()
            # print("optimal agent chosen, all possible states length: ", len(self.all_possible_states))
            self.policy = self.value_iteration_fast()
        else:
            self.all_possible_states = self.all_possible_raw_states
            self.discount_factor = 1 - np.finfo(np.float32).eps
            # print("not optimal agent chosen, all possible states length: ", len(self.all_possible_states))
            self.policy = self.value_iteration_raw()
        # print(initial)





    def check_if_gas_station_iter(self, taxi_operations, taxi_dict, taxi_name):
        # check for all taxies, if each one's lcoation is 'G', if so, add 'refuel' to actions
        # taxi operations is a dict, gets actions from the conditions
        loc = taxi_dict["location"]
        if self.map[int(loc[0])][int(loc[1])] != "G" or taxi_dict["curr_fuel"] == \
                self.max_fuel_dict[taxi_name]:
            taxi_operations["refuel"] = 0
        return taxi_operations

    def check_if_out_of_borders_iter(self, taxi_operations, taxi_dict, taxi_name):
        # check for all taxies, if their location is an edge of the map, and add legal directions accordingly
        loc = taxi_dict["location"]
        if loc[0] == 0:
            taxi_operations["move up"] = 0
        if loc[0] == len(self.map) - 1:
            taxi_operations["move down"] = 0
        if loc[1] == 0:
            taxi_operations["move left"] = 0
        if loc[1] == len(self.map[0]) - 1:
            taxi_operations["move right"] = 0
        return taxi_operations

    def check_if_near_impassable_iter(self, taxi_operations, taxi_dict, taxi_name):
        # for all taxies, if they have a direction in their operation, check if the movement would result in them being in an 'I' location if the map, if so, remove the direction from their operations
        loc = taxi_dict["location"]
        loc = [int(loc[0]), int(loc[1])]
        if taxi_operations["move left"]:
            if self.map[loc[0]][loc[1] - 1] == "I":
                taxi_operations["move left"] = 0
        if taxi_operations["move right"]:
            if self.map[loc[0]][loc[1] + 1] == "I":
                taxi_operations["move right"] = 0
        if taxi_operations["move up"]:
            if self.map[loc[0] - 1][loc[1]] == "I":
                taxi_operations["move up"] = 0
        if taxi_operations["move down"]:
            if self.map[loc[0] + 1][loc[1]] == "I":
                taxi_operations["move down"] = 0
        return taxi_operations

    def check_if_out_of_fuel_iter(self, taxi_operations, taxi_dict, taxi_name):
        # check for all taxies, if each one's fuel is 0, if so, remove actions including directions
        # taxi operations is a dict, gets actions from the conditions
        if taxi_dict["curr_fuel"] == 0:
            # if the item exists it the list, remove it
            taxi_operations["move left"] = 0
            taxi_operations["move right"] = 0
            taxi_operations["move up"] = 0
            taxi_operations["move down"] = 0
        return taxi_operations


    def check_if_can_pick_up_iter(self, taxi_operations, taxi_dict, taxi_name, state_as_dict):
        # for each taxi, if there isn't a passenger in the location, or if the taxi is full, remove the 'pick up' action
        #if the taxi is full, remove the 'pick up' action
        if taxi_dict["curr_passengers"] == self.capacity_dict[taxi_name]:
            taxi_operations["pick up"] = 0
            return taxi_operations
        else:
            loc = taxi_dict["location"]
            # if there isn't a passenger in the location, remove the 'pick up' action
            # if there is a passenger in 'loc', and his destination is 'loc', remove the 'pick up' action
            for passenger in state_as_dict["passengers"].keys():
                if state_as_dict["passengers"][passenger]["location"] == loc and \
                        state_as_dict["passengers"][passenger]["destination"] != loc:
                    return taxi_operations
            taxi_operations["pick up"] = 0
            return taxi_operations
        ##go over later ^

        return taxi_operations

    def check_if_potential_destination_iter(self, taxi_operations, taxi_dict, passenger_dict, taxi_name):
        # for each taxi, see if the location is not a destination, if so, remove the 'drop off' action
        loc = taxi_dict["location"]
        #for each passenger, if their location is labeled as 'taxi_name'
        #and their destination is 'loc', return the taxi operations
        #if not, remove the 'drop off' action
        for passenger in self.passengers:
            if passenger_dict[passenger]["location"] == taxi_name and \
                    passenger_dict[passenger]["destination"] == loc:
                return taxi_operations
        #if we are here, there are no passengers in the taxi which are going to 'loc'
        #remove the 'drop off' action
        taxi_operations["drop off"] = 0
        return taxi_operations


    def reformat_actions(self, taxi_operations, state_as_dict):
        # change format to (action, taxi, relevant passenger if 'pick up' or 'drop off' or future location if 'move')
        actions = []
        for idx, taxi in enumerate(taxi_operations.keys()):
            actions.append([])
            if taxi_operations[taxi]["pick up"]:
                #get the name of the passenger that can be picked up
                #a passenger that can be picked up must be in the same location as the taxi
                #and their destination must not be the same as their location
                for passenger in state_as_dict["passengers"].keys():
                    if state_as_dict["passengers"][passenger]["location"] == state_as_dict["taxies"][taxi]["location"] and \
                            state_as_dict["passengers"][passenger]["destination"] != state_as_dict["taxies"][taxi]["location"]:
                        actions[idx].append(("pick up", taxi, passenger))


            if taxi_operations[taxi]["drop off"]:
                #get the name of the passenger that can be dropped off
                #a passenger that can be dropped off must be labeled as being in the taxi
                #and their destination must be the same as the taxi's location
                for passenger in state_as_dict["passengers"].keys():
                    if state_as_dict["passengers"][passenger]["location"] == taxi and \
                            state_as_dict["passengers"][passenger]["destination"] == state_as_dict['taxies'][taxi]["location"]:
                        actions[idx].append(("drop off", taxi, passenger))

            if taxi_operations[taxi]["move right"]:
                actions[idx].append(("move", taxi, (
                    state_as_dict["taxies"][taxi]["location"][0], state_as_dict["taxies"][taxi]["location"][1] + 1)))
            if taxi_operations[taxi]["move left"]:
                actions[idx].append(("move", taxi, (
                    state_as_dict["taxies"][taxi]["location"][0], state_as_dict["taxies"][taxi]["location"][1] - 1)))
            if taxi_operations[taxi]["move up"]:
                actions[idx].append(("move", taxi, (
                    state_as_dict["taxies"][taxi]["location"][0] - 1, state_as_dict["taxies"][taxi]["location"][1])))
            if taxi_operations[taxi]["move down"]:
                actions[idx].append(("move", taxi, (
                    state_as_dict["taxies"][taxi]["location"][0] + 1, state_as_dict["taxies"][taxi]["location"][1])))
            if taxi_operations[taxi]["refuel"]:
                actions[idx].append(("refuel", taxi))
            if taxi_operations[taxi]["wait"]:
                actions[idx].append(("wait", taxi))
        return actions

    def create_all_available_actions(self, reformatted_actions):
        # return cartesian product of all actions
        return list(itertools.product(*reformatted_actions))

    def remove_illegal_actions(self, actions, state_as_dict):
        updated_actions = []
        for action in actions:
            list_of_locations = []
            list_of_actions = []
            for action_of_single_taxi in action:
                list_of_actions.append(action_of_single_taxi[0])
                if action_of_single_taxi[0] == "move":
                    list_of_locations.append(action_of_single_taxi[2])
                else:
                    # append the current location of the taxi
                    current_loc = state_as_dict["taxies"][action_of_single_taxi[1]]["location"]
                    list_of_locations.append(tuple(current_loc))

            # # if all the actions are "wait", continue
            # if list_of_actions == ["wait"] * len(list_of_actions):
            #     continue

            # if all the locations are unique, then the action is legal, add it to the list of updated_actions
            if len(list_of_locations) == len(set(list_of_locations)):
                updated_actions.append(action)
        return updated_actions

    def actions(self, state):
        state_as_dict = ast.literal_eval(state)
        taxi_operations = {}

        for taxi in state_as_dict["taxies"].keys():
            taxi_operations[taxi] = self.operations.copy()

        # check gas stations
        for taxi in state_as_dict["taxies"].keys():
            # check if potential destination
            taxi_operations[taxi] = self.check_if_potential_destination_iter(taxi_operations[taxi],
                                                                             state_as_dict["taxies"][taxi],
                                                                             state_as_dict["passengers"], taxi)
            #if it is a potential destination, then there's no need to check other actions, since dropping off is first priority
            #therefore, set all other actions to 0
            #and continue to the next taxi
            if taxi_operations[taxi]["drop off"]:
                taxi_operations[taxi]["pick up"] = 0
                taxi_operations[taxi]["move right"] = 0
                taxi_operations[taxi]["move left"] = 0
                taxi_operations[taxi]["move up"] = 0
                taxi_operations[taxi]["move down"] = 0
                taxi_operations[taxi]["refuel"] = 0
                taxi_operations[taxi]["wait"] = 0
                continue

            taxi_operations[taxi] = self.check_if_gas_station_iter(taxi_operations[taxi], state_as_dict["taxies"][taxi],
                                                                   taxi)
            # check if out of borders
            taxi_operations[taxi] = self.check_if_out_of_borders_iter(taxi_operations[taxi],
                                                                      state_as_dict["taxies"][taxi], taxi)
            # check if near impassable
            taxi_operations[taxi] = self.check_if_near_impassable_iter(taxi_operations[taxi],
                                                                       state_as_dict["taxies"][taxi], taxi)
            # check if out of fuel
            taxi_operations[taxi] = self.check_if_out_of_fuel_iter(taxi_operations[taxi], state_as_dict["taxies"][taxi],
                                                                   taxi)

            # check if passenger in location
            taxi_operations[taxi] = self.check_if_can_pick_up_iter(taxi_operations[taxi],
                                                                   state_as_dict["taxies"][taxi],
                                                                   taxi, state_as_dict)

        actions_reformatted = self.reformat_actions(taxi_operations, state_as_dict)
        actions = self.create_all_available_actions(actions_reformatted)
        actions = self.remove_illegal_actions(actions, state_as_dict)
        if state == str(self.initial):
            return tuple(actions)
        actions = actions + [("reset"),]
        return tuple(actions)

    def result(self, state, action):
        if action == "reset":
            return [(1, str(self.initial))]
        if action == "terminate":
            return "terminate"
        state_as_dict = ast.literal_eval(state)
        for action_of_single_taxi in action:
            taxi_key = action_of_single_taxi[1]
            action_to_execute = action_of_single_taxi[0]
            loc = state_as_dict["taxies"][taxi_key]["location"]
            if action_to_execute == "move":
                state_as_dict["taxies"][taxi_key]["location"] = action_of_single_taxi[2]
                # remove one unit of fuel
                state_as_dict["taxies"][taxi_key]["curr_fuel"] -= 1
            elif action_to_execute == "pick up":
                state_as_dict["taxies"][taxi_key]["curr_passengers"] += 1
                #set the location of the passenger to the taxi key
                state_as_dict["passengers"][action_of_single_taxi[2]]["location"] = taxi_key
            elif action_to_execute == "drop off":
                state_as_dict["taxies"][taxi_key]["curr_passengers"] -= 1
                #set the location of the passenger to location of the taxi
                state_as_dict["passengers"][action_of_single_taxi[2]]["location"] = loc
            elif action_to_execute == "refuel":
                state_as_dict["taxies"][taxi_key]["curr_fuel"] = self.max_fuel_dict[taxi_key]
        #create a list of tuples
        #each tuple is (p, s) when s is the state and p is the probability of the state
        #probabilities are only relevant for passengers' destinations
        probabilities_and_states = []
        original_destinations = {}
        for passenger in state_as_dict["passengers"].keys():
            original_destinations[passenger] = state_as_dict["passengers"][passenger]["destination"]

        for scenario in product_dict(self.destinations_by_passenger):
            #create a deepcopy of the state
            p = 1
            for passenger in scenario.keys():
                state_as_dict["passengers"][passenger]["destination"] = scenario[passenger]
                p *= self.probabilities_by_passenger[passenger][original_destinations[passenger] == scenario[passenger]]
            probabilities_and_states.append((p, str(state_as_dict)))
        return probabilities_and_states


    def calculate_reward(self, action):
        reward = 0
        for action_of_single_taxi in action:
            if action_of_single_taxi == "reset":
                return 0
            action_to_execute = action_of_single_taxi[0]
            if action_to_execute in self.reward_dict.keys():
                reward += self.reward_dict[action_to_execute]
        return reward


    def expected_reward(self, state, turns_to_go, action, V_old):
        if turns_to_go == 1:
            return 0
        p_and_s = self.all_results_and_probs_by_raw_state_action[(state, action)] #(0.2, somestate)
        if p_and_s == "reset":
            return V_old[(str(self.initial),turns_to_go - 1)]
        if p_and_s == "terminate":
            return "terminate"
        sum = 0
        for p, s in p_and_s:
            sum += p * V_old[(s, turns_to_go - 1)]
        return sum

    def expected_reward_non_optimal(self, state, action, V_old):
        p_and_s = self.all_results_and_probs_by_raw_state_action[(state, action)] #(0.2, somestate)
        if p_and_s == "reset":
            return V_old[str(self.initial)]
        if p_and_s == "terminate":
            return "terminate"
        sum = 0
        for p, s in p_and_s:
            sum += p * V_old[s]
        return sum

    def value_iteration_raw(self): ##CHANGE TO MATCH DICT OF (STATE, TURN) -> VALUE
        V = {}
        policy = {}
        for state in self.all_possible_states:
            V[state] = 0
        for i in range(self.N):
            V_new = {}
            for state in self.all_possible_states:
                to_max = []
                for action in self.all_actions_by_raw_state[state]:
                    future_reward = self.expected_reward_non_optimal(state, action, V)
                    action_reward = self.calculate_reward(action)
                    to_max.append(action_reward + self.discount_factor*future_reward)
                V_new[state] = max(to_max)
                policy[state] = self.all_actions_by_raw_state[state][np.argmax(to_max)]
            V = V_new
        #print(V[str(self.initial)])
        return policy


    def value_iteration_fast(self):
        V = {}
        policy = {}
        for state in self.all_possible_states:
            to_max = []
            raw_state = state[0]
            turns_to_go = state[1]
            for action in self.all_actions_by_raw_state[raw_state]:
                future_reward = self.expected_reward(raw_state, turns_to_go, action, V) if turns_to_go > 0 else 0
                action_reward = self.calculate_reward(action)
                to_max.append(action_reward + self.discount_factor * future_reward)
            V[state] = max(to_max)
            policy[state] = self.all_actions_by_raw_state[raw_state][np.argmax(to_max)]
            #print value of initial state
        #print(V[(str(self.initial), self.N)])
        return policy




    def act(self, state):
        turns_to_go = state["turns to go"]
        clean_dict = {"taxies": {}, "passengers": {}}
        for taxi in state["taxis"].keys():
            taxi_info = state["taxis"][taxi]
            clean_dict["taxies"][taxi] = {"location": taxi_info["location"],
                                          "curr_passengers": self.capacity_dict[taxi] - taxi_info["capacity"],
                                          "curr_fuel": taxi_info["fuel"],
                                          }
        for passenger in state["passengers"].keys():
            passenger_info = state["passengers"][passenger]
            clean_dict["passengers"][passenger] = {"location": passenger_info["location"],
                                                   "destination": passenger_info["destination"]}
        clean_dict_str = str(clean_dict)
        initial_str = str(self.initial)
        return self.policy[clean_dict_str,turns_to_go]



class TaxiAgent(OptimalTaxiAgent):

    #def print_all_node_attributes(self, G):
        #for node in G.nodes():
            #print(node, G.nodes[node])

    def create_graph(self, map):
        graph = {}
        for i in range(len(map)):
            for j in range(len(map[0])):
                graph[(i, j)] = {}
                if map[i][j] != 'I':
                    if i > 0 and map[i - 1][j] != 'I':
                        graph[(i, j)][(i - 1, j)] = 1
                    if i < len(map) - 1 and map[i + 1][j] != 'I':
                        graph[(i, j)][(i + 1, j)] = 1
                    if j > 0 and map[i][j - 1] != 'I':
                        graph[(i, j)][(i, j - 1)] = 1
                    if j < len(map[0]) - 1 and map[i][j + 1] != 'I':
                        graph[(i, j)][(i, j + 1)] = 1
        return graph

    def state_to_graph(self, state):
        self.initial_graph = self.create_graph(state["map"])
        self.initial_graph = nx.Graph(self.initial_graph).to_undirected()
        unique_notes_and_values = {}
        for note in self.initial_graph.nodes():
            unique_notes_and_values[note] = []
        for taxi in state["taxis"].keys():
            taxi_info = state["taxis"][taxi]
            unique_notes_and_values[taxi_info["location"]]+= ['taxi']
        #in the map, places that are marked with 'I' should be valued with 'I'
        #places that are marked with 'G' should be valued with 'G'
        #go over all the places in the map (state["map"])
        #if the place is marked with 'I' or 'G', add it to the unique_notes_and_values
        for i in range(len(state["map"])):
            for j in range(len(state["map"][0])):
                if state["map"][i][j] == 'I':
                    unique_notes_and_values[(i,j)] += ['I']
                elif state["map"][i][j] == 'G':
                    unique_notes_and_values[(i,j)] += ['G']
        nx.set_node_attributes(self.initial_graph, unique_notes_and_values, 'value')
        return

    def choose_taxi_and_passenger(self, state):
        #choose a taxi and a passenger
        #return the taxi and the passenger
        #choose a taxi and passenger in the following way:
        #we want a taxi that has a clear path to the passenger location
        #we want a passenger that has a clear path to their destination
        #the total distance of the paths should be lower than the fuel of the taxi
        #if there are multiple taxis and passengers that satisfy the above conditions, choose the pair with the shortest path
        #a clear path is a path that does not contain any 'I' or 'G' nodes, as well as a path that does not contain any other taxis
        #we can see the attributes by using the attribute 'value' of the nodes
        potential_taxis_and_passengers = []
        for taxi in state["taxis"].keys():
            taxi_info = state["taxis"][taxi]
            new_graph = copy.deepcopy(self.initial_graph)
            #remove the 'taxi' property from the node that the taxi is currently in
            new_graph.nodes[taxi_info["location"]]['value'].remove('taxi')
            other_taxi_locations = [node for node in new_graph.nodes() if 'taxi' in new_graph.nodes[node]['value']]
            #isolate other taxi locations in the graph by removing all the edges that connect to other taxi locations
            #however, we do not want to entirely remove those nodes
            edges_to_remove = [(node1, node2) for node1, node2 in new_graph.edges if
                               node1 in other_taxi_locations or node2 in other_taxi_locations]
            new_graph.remove_edges_from(edges_to_remove)

            for passenger in state["passengers"].keys():
                passenger_info = state["passengers"][passenger]
                try:
                    taxi_path = nx.shortest_path(new_graph, taxi_info["location"], passenger_info["location"])
                    passenger_path = nx.shortest_path(new_graph, passenger_info["location"], passenger_info["destination"])
                except nx.NetworkXNoPath:
                    continue
                taxi_path_length = len(taxi_path) - 1
                passenger_path_length = len(passenger_path) - 1
                # if taxi_path_length + passenger_path_length <= taxi_info["fuel"]:
                potential_taxis_and_passengers.append((taxi, passenger, taxi_path_length + passenger_path_length))
        if len(potential_taxis_and_passengers) == 0:
            #todo: handle this case
            return None, None
        else:
            return min(potential_taxis_and_passengers, key=lambda x: x[2])[0:2]

    def remove_unvaluable_passengers(self, state_their_format):
        for passenger in self.unvaluable_passengers:
            del state_their_format["passengers"][passenger]
        return state_their_format

    def remove_unvaluable_taxis(self, state_their_format):
        unvaluable_taxis_locations = []
        for taxi in self.unvaluable_taxis:
            location = state_their_format["taxis"][taxi]["location"]
            unvaluable_taxis_locations.append(location)
            del state_their_format["taxis"][taxi]
        #remove the edges from the graph that connect to the unvaluable taxis
        for location in unvaluable_taxis_locations:
            state_their_format["map"][location[0]][location[1]] = 'I'
        return state_their_format

    def convert_action_to_real_action(self, action):
        #for all the taxis that are not valuable, we want to do nothing
        #so their action is always 'wait'
        #for the valuable taxis, we want to do the action that is given
        if action == "reset":
            return action
        actual_action = []
        for taxi in self.unvaluable_taxis:
            actual_action.append(("wait",taxi))
        for taxi_action in action:
            actual_action.append(taxi_action)
        return tuple(actual_action)


    def act(self, state):
        state = copy.deepcopy(state)
        self.remove_unvaluable_passengers(state)
        self.remove_unvaluable_taxis(state)
        #remove all the keys but 'taxis' and 'passengers' from the state
        clean_dict = {"taxies": {}, "passengers": {}}
        for taxi in state["taxis"].keys():
            taxi_info = state["taxis"][taxi]
            clean_dict["taxies"][taxi] = {"location": taxi_info["location"],
                                          "curr_passengers": self.capacity_dict[taxi] - taxi_info["capacity"],
                                          "curr_fuel": taxi_info["fuel"],
                                          }
        for passenger in state["passengers"].keys():
            passenger_info = state["passengers"][passenger]
            clean_dict["passengers"][passenger] = {"location": passenger_info["location"],
                                                   "destination": passenger_info["destination"]}
        clean_dict_str = str(clean_dict)
        non_optimal_action = self.policy[str(clean_dict)]
        return self.convert_action_to_real_action(non_optimal_action)



    def __init__(self,initial_state):
        #print("Non-optimal agent initialized")
        self.iterations = 150
        self.state_to_graph(initial_state)
        chosen_taxi, chosen_passenger = self.choose_taxi_and_passenger(initial_state)
        self.unvaluable_passengers = [passenger for passenger in initial_state["passengers"].keys() if passenger != chosen_passenger]
        self.unvaluable_taxis = [taxi for taxi in initial_state["taxis"].keys() if taxi != chosen_taxi]
        pseudo_initial = ast.literal_eval(str(initial_state))
        pseudo_initial = self.remove_unvaluable_taxis(pseudo_initial)
        pseudo_initial = self.remove_unvaluable_passengers(pseudo_initial)
        pseudo_initial['turns to go'] = self.iterations
        super().__init__(pseudo_initial, for_optimal_policy=False)


