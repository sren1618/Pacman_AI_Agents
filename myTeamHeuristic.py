# myTeam.py
# ---------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
#
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).
import math

from captureAgents import CaptureAgent
import random, time, util
from game import Directions
import game


#################
# Team creation #
#################

def createTeam(firstIndex, secondIndex, isRed,
               first='AgentOffensive', second='AgentDefensive'):
    """
  This function should return a list of two agents that will form the
  team, initialized using firstIndex and secondIndex as their agent
  index numbers.  isRed is True if the red team is being created, and
  will be False if the blue team is being created.

  As a potentially helpful development aid, this function can take
  additional string-valued keyword arguments ("first" and "second" are
  such arguments in the case of this function), which will come from
  the --redOpts and --blueOpts command-line arguments to capture.py.
  For the nightly contest, however, your team will be created without
  any extra arguments, so you should make sure that the default
  behavior is what you want for the nightly contest.
  """

    # The following line is an example only; feel free to change it.
    return [eval(first)(firstIndex), eval(second)(secondIndex)]


##########
# Agents #
##########

class DummyAgent(CaptureAgent):
    """
    A Dummy agent to serve as an example of the necessary agent structure.
    You should look at baselineTeam.py for more details about how to
    create an agent as this is the bare minimum.
    """

    def registerInitialState(self, gameState):
        """
        This method handles the initial setup of the
        agent to populate useful fields (such as what team
        we're on).

        A distanceCalculator instance caches the maze distances
        between each pair of positions, so your agents can use:
        self.distancer.getDistance(p1, p2)

        IMPORTANT: This method may run for at most 15 seconds.
        """

        '''
        Make sure you do not delete the following line. If you would like to
        use Manhattan distances instead of maze distances in order to save
        on initialization time, please take a look at
        CaptureAgent.registerInitialState in captureAgents.py.
        '''
        CaptureAgent.registerInitialState(self, gameState)

        '''
        Your initialization code goes here, if you need any.
        '''
        self.boundaries = self.mapBoundaries(gameState)
        self.isRed = self.red
        self.capsulesNum = len(self.getCapsules(gameState))
        mapWidth = gameState.data.layout.width
        self.middleLine = int(mapWidth / 2) - 1 if self.isRed else int(mapWidth / 2)
        self.defendedFoodNumber = len(self.getFoodYouAreDefending(gameState).asList())

    def chooseAction(self, gameState):
        """
    Picks among actions randomly.
    """
        actions = gameState.getLegalActions(self.index)

        '''
    You should change this in your own agent.
    '''

        return random.choice(actions)

    def mapBoundaries(self, gameState):
        mapWidth = gameState.data.layout.width
        middleWidth = int(mapWidth / 2) - 1 if self.red else int(mapWidth / 2)
        mapHeight = gameState.data.layout.height
        walls = gameState.getWalls()
        boundaries = []
        for height in range(mapHeight):
            if not walls[middleWidth][height]:
                boundaries.append((middleWidth, height))
        return boundaries


class AgentOffensive(DummyAgent):
    carriedFoods = 0

    def chooseAction(self, gameState):
        self.goal = None
        agentPosition = gameState.getAgentState(self.index).getPosition()

        if self.capsulesNum > 0:
            if len(self.getCapsules(gameState)) >= self.capsulesNum:
                self.goal = self.getCapsules(gameState)[0]
            else:
                if self.carriedFoods < 5:
                    foodList = self.getFood(gameState).asList()
                    self.goal = min(foodList, key=lambda pos: self.getMazeDistance(agentPosition, pos))
                else:
                    self.goal = min(self.boundaries, key=lambda pos: self.getMazeDistance(agentPosition, pos))
                if agentPosition in self.boundaries:
                    self.capsulesNum -= 1
        else:
            if self.carriedFoods == 3 or len(self.getFood(gameState).asList()) <= 2:
                self.goal = min(self.boundaries, key=lambda pos: self.getMazeDistance(agentPosition, pos))
            else:
                foodList = self.getFood(gameState).asList()
                self.goal = min(foodList, key=lambda pos: self.getMazeDistance(agentPosition, pos))

        opponents = DummyAgent.getOpponents(self, gameState)
        problem = offensiveSearchProblem(gameState, opponents, self.middleLine, self.isRed, self.goal, self.index)
        actions = self.aStarSearch(problem)

        if actions == []:
            actions = gameState.getLegalActions(self.index)
            return random.choice(actions)
        else:
            action = actions[0]
            dx, dy = game.Actions.directionToVector(action)
            x, y = gameState.getAgentState(self.index).getPosition()
            new_x, new_y = int(x + dx), int(y + dy)
            if (new_x, new_y) == self.goal:
                self.goal = None
            if self.getFood(gameState)[new_x][new_y]:
                self.carriedFoods += 1
            elif (new_x, new_y) in self.boundaries:
                self.carriedFoods = 0
            return actions[0]
    #aStarSearch copied from baseline agent code
    def aStarSearch(self, problem):
        """Search the node that has the lowest combined cost and heuristic first."""
        from util import PriorityQueue
        myPQ = util.PriorityQueue()
        startState = problem.getStartState()
        # print(f"start states {startState}")
        startNode = (startState, '', 0, [])
        heuristic = problem._opponentDistance
        myPQ.push(startNode, heuristic(startState))
        visited = set()
        best_g = dict()
        while not myPQ.isEmpty():
            node = myPQ.pop()
            state, action, cost, path = node
            if (not state in visited) or cost < best_g.get(str(state)):
                visited.add(state)
                best_g[str(state)] = cost
                if problem.isGoalState(state):
                    path = path + [(state, action)]
                    actions = [action[1] for action in path]
                    del actions[0]
                    return actions
                for succ in problem.getSuccessors(state):
                    succState, succAction, succCost = succ
                    newNode = (succState, succAction, cost + succCost, path + [(node, action)])
                    myPQ.push(newNode, heuristic(succState) + cost + succCost)
        return []


class AgentDefensive(DummyAgent):
    goUp = False
    def chooseAction(self, gameState):
        agentPosition = gameState.getAgentState(self.index).getPosition()
        closestOpponent = self.isOpponentsOnMySide(gameState, agentPosition)
        foodList = self.getFoodYouAreDefending(gameState).asList()

        # Chase your opponent.
        if closestOpponent is not None:
            problem = defensiveSearchProblem(gameState, self.middleLine, self.isRed, closestOpponent, self.index)
            actions = self.aStarSearch(problem)
            return actions[0]
        elif len(foodList) < self.defendedFoodNumber // 2:
            if agentPosition in foodList:
                foodList.remove(agentPosition)
            # food = max(foodList, key=lambda pos: self.getMazeDistance(agentPosition, pos))
            food = random.choice(foodList)
            problem = defensiveSearchProblem(gameState, self.middleLine, self.isRed, food, self.index)
            actions = self.aStarSearch(problem)
            return actions[0]
        # Patrol at the border
        else:
            middleIndex = len(self.boundaries) // 2
            if middleIndex > 3:
                startIndex = middleIndex - 3
                endIndex = middleIndex + 3
            else:
                startIndex = 0
                endIndex = -1
            if self.goUp:
                if agentPosition == self.boundaries[startIndex]:
                    self.goUp = False
                    patrolPosition = self.boundaries[endIndex]
                else:
                    patrolPosition = self.boundaries[startIndex]
            else:
                if agentPosition == self.boundaries[endIndex]:
                    self.goUp = True
                    patrolPosition = self.boundaries[startIndex]
                else:
                    patrolPosition = self.boundaries[endIndex]
            # patrolPosition = random.choice(available_boundaries)
            problem = defensiveSearchProblem(gameState, self.middleLine, self.isRed, patrolPosition, self.index)
            actions = self.aStarSearch(problem)
            return actions[0]

    def isOpponentsOnMySide(self, gameState, agentPosition):
        opponents = DummyAgent.getOpponents(self, gameState)
        closestOpponent = None
        closestOpponentDistance = 99999

        for opponent in opponents:
            opponentPosition = gameState.getAgentPosition(opponent)
            # opponent observable
            if opponentPosition is not None:
                if (self.isRed and opponentPosition[0] <= self.middleLine) or (
                        not self.isRed and opponentPosition[0] >= self.middleLine):
                    agentToOpponentDistance = self.getMazeDistance(agentPosition, opponentPosition)
                    if agentToOpponentDistance < closestOpponentDistance:
                        closestOpponent = opponentPosition
                        closestOpponentDistance = agentToOpponentDistance
        return closestOpponent

    # aStarSearch copied from baseline agent code
    def aStarSearch(self, problem):
        """Search the node that has the lowest combined cost and heuristic first."""

        from util import PriorityQueue
        myPQ = util.PriorityQueue()
        startState = problem.getStartState()
        # print(f"start states {startState}")
        startNode = (startState, '', 0, [])
        heuristic = problem._manhattanDistance
        myPQ.push(startNode, heuristic(startState))
        visited = set()
        best_g = dict()
        while not myPQ.isEmpty():
            node = myPQ.pop()
            state, action, cost, path = node
            if (not state in visited) or cost < best_g.get(str(state)):
                visited.add(state)
                best_g[str(state)] = cost
                if problem.isGoalState(state):
                    path = path + [(state, action)]
                    actions = [action[1] for action in path]
                    del actions[0]
                    return actions
                for succ in problem.getSuccessors(state):
                    succState, succAction, succCost = succ
                    newNode = (succState, succAction, cost + succCost, path + [(node, action)])
                    myPQ.push(newNode, heuristic(succState) + cost + succCost)
        return []

#implemented problem based on basline problem
class offensiveSearchProblem:

    def __init__(self, gameState, opponents, middleLine, isRed, goal, agentIndex=0):
        x, y = gameState.getAgentState(agentIndex).getPosition()
        self.agentCurrentPosition = int(x), int(y)
        self.gameState = gameState
        self.goal = goal
        self.middleLine = middleLine
        self.isRed = isRed
        self.walls = gameState.getWalls()
        self.opponents = opponents

    def getStartState(self):
        return self.agentCurrentPosition

    def isGoalState(self, state):
        return state == self.goal

    def getSuccessors(self, state):
        successors = []
        for action in [game.Directions.NORTH, game.Directions.SOUTH, game.Directions.EAST, game.Directions.WEST]:
            x, y = state
            dx, dy = game.Actions.directionToVector(action)
            nextx, nexty = int(x + dx), int(y + dy)
            if not self.walls[nextx][nexty]:
                nextState = (nextx, nexty)
                successors.append((nextState, action, 1))
        return successors

    def _opponentDistance(self, current):
        opponentDistance = 0
        for opponent in self.opponents:
            opponentPosition = self.gameState.getAgentPosition(opponent)
            if opponentPosition is not None:
                if (self.isRed and opponentPosition[0] > self.middleLine) or (
                        not self.isRed and opponentPosition[0] < self.middleLine):
                    distance = util.manhattanDistance(current, opponentPosition)
                    if opponentDistance < distance < 2:
                        opponentDistance = 9999
        return opponentDistance + util.manhattanDistance(current, self.goal)

#implemented problem based on basline problem
class defensiveSearchProblem:
    def __init__(self, gameState, middleLine, isRed, goal, agentIndex=0):
        x, y = gameState.getAgentState(agentIndex).getPosition()
        self.agentCurrentPosition = int(x), int(y)
        self.middleLine = middleLine
        self.isRed = isRed
        self.goal = goal
        self.walls = gameState.getWalls()

    def getStartState(self):
        return self.agentCurrentPosition

    def isGoalState(self, state):
        return state == self.goal

    def getSuccessors(self, state):
        successors = []
        for action in [game.Directions.NORTH, game.Directions.SOUTH, game.Directions.EAST, game.Directions.WEST]:
            x, y = state
            dx, dy = game.Actions.directionToVector(action)
            nextx, nexty = int(x + dx), int(y + dy)
            if not self.walls[nextx][nexty]:
                if (self.isRed and nextx <= self.middleLine) or (
                        not self.isRed and nextx >= self.middleLine):
                    nextState = (nextx, nexty)
                    successors.append((nextState, action, 1))
        return successors

    def _manhattanDistance(self, current):
        return util.manhattanDistance(current, self.goal)