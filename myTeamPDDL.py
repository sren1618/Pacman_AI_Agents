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


from captureAgents import CaptureAgent
import random, time, util
from game import Directions
import game
import os
import re
import subprocess


filePath = os.path.dirname(os.path.abspath(__file__))
domainOffensive = f"{filePath}/domain_offensive.pddl"
domainDefensive = f"{filePath}/domain_defensive.pddl"
ffPath = f"{filePath}/ff"

#################
# Team creation #
#################

def createTeam(firstIndex, secondIndex, isRed,
               first = 'pddlOffensiveAgent', second = 'pddlDefensiveAgent'):
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
  # path = f"{filePath}/ffmac"
  os.chmod(ffPath, os.stat(ffPath).st_mode | 0o111)
  # The following line is an example only; feel free to change it.
  return [eval(first)(firstIndex), eval(second)(secondIndex)]

##########
# Agents #
##########
class pddlAgent(CaptureAgent):
  def registerInitialState(self, gameState):
    CaptureAgent.registerInitialState(self, gameState)
    self.boundaries = self.mapBoundaries(gameState)
    self.isRed = self.red
    self.capsulesNum = len(self.getCapsules(gameState))
    mapWidth = gameState.data.layout.width
    mapHeight = gameState.data.layout.height
    self.middleLine = int(mapWidth / 2) - 1 if self.isRed else int(mapWidth / 2)
    self.middleHeight = int(mapHeight / 2)
    self.defendedFoodNumber = len(self.getFoodYouAreDefending(gameState).asList())

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

  def foodsDistribution(self, gameState, type):
    y_line = self.middleHeight
    group1 = []
    group2 = []
    group3 = []
    group4 = []
    if type == 'def':
      foods = self.getFoodYouAreDefending(gameState).asList()
      if self.isRed:
        x_line = int(self.middleLine / 2)
      else:
        x_line = int(self.middleLine * 1.5)
    else:
      foods = self.getFood(gameState).asList()
      if self.isRed:
        x_line = int(self.middleLine * 1.5)
      else:
        x_line = int(self.middleLine / 2)
    for x, y in foods:
      if x > x_line and y > y_line:
        group1.append((x, y))
      elif x > x_line and y < y_line:
        group2.append((x, y))
      elif x <= x_line and y <= y_line:
        group3.append((x, y))
      elif x <= x_line and y >= y_line:
        group4.append((x, y))
    return [group1, group2, group3, group4]



class pddlOffensiveAgent(pddlAgent):
  carriedFoods = 0
  def createOffensiveDomianFile(self):
    domainOffensiveFile = open(domainOffensive, "w")
    domainContent = """
    (define (domain offensiveAgent)

      (:requirements
          :typing
          :negative-preconditions
      )
  
      (:types
          cells foods
      )
  
      (:predicates
          ;agent's cell location
          (at-agent ?loc - cells)
          
          ;food's cell location
          (at-food ?loc - cells ?foo - foods)
          
          ;Indicates if a cell location has a ghost
          (has-ghost ?loc - cells)
          
          ;Indicates if a cell location has a capsule
          (has-capsule ?loc - cells)
  
          ;Indicates if a agent carries food
          (is-carrying)
          
          ;connects cells
          (connected ?from ?to - cells)
         
          ;Indicates if a agent has eaten a capsule
          (is-capsule-eaten)
      )
  
      ;Agent can move the location if there is no ghost and wall
      (:action move
          :parameters (?from ?to - cells)
          :precondition (and
              (at-agent ?from)
              (connected ?from ?to)
              (not (has-ghost ?to))                    
          )
          :effect (and
              (at-agent ?to)
              (not (at-agent ?from))               
          )
      )
  
      ;Agent can move the location even there is ghost when has eatn a capsule
      (:action move-with-capsule
          :parameters (?from ?to - cells)
          :precondition (and
              (at-agent ?from)
              (connected ?from ?to)
              (is-capsule-eaten)                
          )
          :effect (and
              (at-agent ?to)
              (not (at-agent ?from))               
          )
      )
      
      ;Agent can eat a food if there is a food in the location
      (:action eat-food
          :parameters (?loc - cells ?foo - foods)
          :precondition (and
              (at-agent ?loc)
              (at-food ?loc ?foo)
          )
          :effect (and
              (is-carrying)
              (not (at-food ?loc ?foo))
          )
      )
  
      ;Agent can eat a capsule if there is a capsule in the location
      (:action eat-capsule
          :parameters (?loc - cells)
          :precondition (and
              (at-agent ?loc)
              (has-capsule ?loc)                      
          )
          :effect (and
              (is-capsule-eaten)
              (not (has-capsule ?loc))                 
          )
      )
    )
    """
    domainOffensiveFile.write(domainContent)
    domainOffensiveFile.close()

  def createOffensiveProblemFile(self, gameState):
    cellsCoordinate = gameState.getWalls().asList(False)
    agentsCoordinate = gameState.getAgentPosition(self.index)
    foodsCoordinate = self.getFood(gameState).asList()
    capsulesCoordinate = self.getCapsules(gameState)
    opponentsCoordinate = [gameState.getAgentPosition(i) for i in self.getOpponents(gameState)]
    scared = min([gameState.getAgentState(i).scaredTimer for i in self.getOpponents(gameState)])

    cellsList = ['cell{}_{}'.format(t[0], t[1]) for t in cellsCoordinate]
    connections = []
    for cell in cellsCoordinate:
      if (cell[0]+1, cell[1]) in cellsCoordinate:
        connection = '(connected cell{}_{} cell{}_{})\n\t\t'.format(cell[0], cell[1], cell[0]+1, cell[1])
        connections.append(connection)
      if (cell[0], cell[1]+1) in cellsCoordinate:
        connection = '(connected cell{}_{} cell{}_{})\n\t\t'.format(cell[0], cell[1], cell[0], cell[1]+1)
        connections.append(connection)
      if (cell[0]-1, cell[1]) in cellsCoordinate:
        connection = '(connected cell{}_{} cell{}_{})\n\t\t'.format(cell[0], cell[1], cell[0]-1, cell[1])
        connections.append(connection)
      if (cell[0], cell[1]-1) in cellsCoordinate:
        connection = '(connected cell{}_{} cell{}_{})\n\t\t'.format(cell[0], cell[1], cell[0], cell[1]-1)
        connections.append(connection)
    foodsList = ['food{}'.format(i) for i in range(len(foodsCoordinate))]
    foods = ["(at-food cell{}_{} food{})\n\t\t".format(t[0], t[1], index) for index, t in enumerate(foodsCoordinate)]
    agent = '(at-agent cell{}_{})\n\t\t'.format(agentsCoordinate[0], agentsCoordinate[1])
    capsules = ['(has-capsule cell{}_{})\n\t\t'.format(capsule[0], capsule[1]) for capsule in capsulesCoordinate]
    opponents = [f"(has-ghost cell{opponent[0]}_{opponent[1]})\n\t\t" for opponent in opponentsCoordinate if opponent is not None]

    cells_str = '  '.join(cellsList) + ' - cells'
    foods_str = '  '.join(foodsList) + ' - foods'
    foods_location_str = ''.join(foods)
    connections_str = ''.join(connections)
    if opponents:
      opponents_str = ''.join(opponents)
    else:
      opponents_str = '\n'
    capsules_str = ''.join(capsules)
    goalStr = self.setOffensiveAgentGoal(gameState)
    if scared >0:
      scared_str = '(is-capsule-eaten)\n\t\t'
    else:
      scared_str = '\n'
    problem_str = """
    (define (problem problem_offensive)
      (:domain offensiveAgent)
      (:objects
        {}
        {}
      )
      (:init
        {}
        {}
        {}
        {}
        {}
        {}
      )
      (:goal(and
        {}
      ))
    )       
    """.format(cells_str, foods_str, agent, capsules_str, scared_str, opponents_str, foods_location_str, connections_str, goalStr)
    problem_file = open(f"{filePath}/problem_offensive.pddl", "w")
    problem_file.write(problem_str)
    problem_file.close()

  def setOffensiveAgentGoal(self,gameState):
    agentPosition = gameState.getAgentState(self.index).getPosition()
    foodListExcludeOppBlock = self.getBestOffensiveFood(gameState)
    foodList = self.getFood(gameState).asList()
    if self.capsulesNum > 0:
      if len(self.getCapsules(gameState)) >= self.capsulesNum:
        goal = min(self.getCapsules(gameState), key=lambda pos: self.getMazeDistance(agentPosition, pos))
      else:
        if self.carriedFoods < 5:
          goal = min(foodList, key=lambda pos: self.getMazeDistance(agentPosition, pos))
        else:
          goal = min(self.boundaries, key=lambda pos: self.getMazeDistance(agentPosition, pos))
        if agentPosition in self.boundaries:
          self.capsulesNum -= 1
    elif len(foodListExcludeOppBlock[0]) >= 1:
      goal = min(foodListExcludeOppBlock[0], key=lambda pos: self.getMazeDistance(agentPosition, pos))
      if self.carriedFoods == 3 or len(self.getFood(gameState).asList()) <= 2:
        goal = min(self.boundaries, key=lambda pos: self.getMazeDistance(agentPosition, pos))
    else:
      if self.carriedFoods == 3 or len(self.getFood(gameState).asList()) <= 2:
        goal = min(self.boundaries, key=lambda pos: self.getMazeDistance(agentPosition, pos))
      else:
        goal = min(foodList, key=lambda pos: self.getMazeDistance(agentPosition, pos))
    return '(at-agent cell{}_{})\n\t\t'.format(goal[0], goal[1])

  def problemSolver(self, gameState):
    (agentX, agentY) = gameState.getAgentState(self.index).getPosition()
    domain = f"{filePath}/domain_offensive.pddl"
    problem = f"{filePath}/problem_offensive.pddl"
    planner = FFPlaner(domain, problem)
    plannedAction = planner.getSolution()
    if plannedAction is not None:
      plannedX = int(plannedAction[0])
      plannedY = int(plannedAction[1])

      if self.getFood(gameState)[plannedX][plannedY]:
        self.carriedFoods += 1
      elif (plannedX, plannedY) in self.boundaries:
        self.carriedFoods = 0
      # elif (plannedX, plannedY) in self.getCapsules(gameState):
      #   self.capsulesNum -= 1

      if plannedX == agentX - 1 and plannedY == agentY:
        return "West"
      elif plannedX == agentX and plannedY == agentY + 1:
        return "North"
      elif plannedX == agentX and plannedY == agentY - 1:
        return "South"
      elif plannedX == agentX + 1 and plannedY == agentY:
        return "East"
      else:
        return "Stop"
    else:
      return "Stop"

  def getMysideOpponents(self, gameState):
    mysideOpponents = []
    agentPosition = gameState.getAgentState(self.index).getPosition()
    opponents = self.getOpponents(gameState)
    for opponent in opponents:
      opponentPosition = gameState.getAgentPosition(opponent)
      if opponentPosition is not None:
        if (self.isRed and opponentPosition[0] >= self.middleLine) or (
                not self.isRed and opponentPosition[0] <= self.middleLine):
          mysideOpponents.append(opponentPosition)
          return min(mysideOpponents, key=lambda pos: self.getMazeDistance(agentPosition, pos))
    return mysideOpponents

  def getBestOffensiveFood(self, gameState):
    agentPosition = gameState.getAgentState(self.index).getPosition()
    opponent = self.getMysideOpponents(gameState)
    foods = self.foodsDistribution(gameState, 'off')
    y_line = self.middleHeight
    if self.isRed:
      x_line = int(self.middleLine * 1.5)
    else:
      x_line = int(self.middleLine / 2)

    if opponent:
      distance = self.getMazeDistance(agentPosition, opponent)
      if distance < 5 and distance >= 2:
        x, y = opponent
        if x > x_line and y > y_line:
          bestFood = [foods[1], foods[2], foods[3]]
          return sorted(bestFood, key=lambda group: len(group), reverse=True)
        elif x > x_line and y < y_line:
          bestFood = [foods[0], foods[2], foods[3]]
          return sorted(bestFood, key=lambda group: len(group), reverse=True)
        elif x <= x_line and y <= y_line:
          bestFood = [foods[0], foods[1], foods[3]]
          return sorted(bestFood, key=lambda group: len(group), reverse=True)
        elif x <= x_line and y >= y_line:
          bestFood = [foods[0], foods[1], foods[2]]
          return sorted(bestFood, key=lambda group: len(group), reverse=True)
      elif len(self.getCapsules(gameState)) > 0 and distance < 2:
          return [self.getCapsules(gameState)]
    return [[]]
  def chooseAction(self, gameState):
    self.createOffensiveDomianFile()
    self.createOffensiveProblemFile(gameState)
    return self.problemSolver(gameState)

class pddlDefensiveAgent(pddlAgent):
  oppList = None
  def createDefensiveDomianFile(self):
    domainDefensiveFile = open(domainDefensive, "w")
    domainContent = """
    (define (domain defensiveAgent)
  
      (:requirements
          :typing
          :negative-preconditions
      )
  
      (:types
          cells opponents
      )
  
      (:predicates             
          ;agent's cell location
          (at-agent ?loc - cells)
  
          ;opponent's cell location
          (at-opponent ?loc - cells ?opp - opponents)
          
          ;Indicates if a cell location has a capsule
          (has-capsule ?loc - cells)
  
          ;connects cells
          (connected ?from ?to - cells)
      )
  
      ;Agent can move the location if there is no wall
      (:action move
          :parameters (?from ?to - cells)
          :precondition (and
              (at-agent ?from)
              (connected ?from ?to)                   
          )
          :effect (and
              (at-agent ?to)
              (not (at-agent ?from))               
          )
      )
  
      ;Agent can eat the opponent if there is a opponent in the location
      (:action eat-opponent
          :parameters (?loc - cells ?opp - opponents)
          :precondition (and
              (at-agent ?loc)
              (at-opponent ?loc ?opp)                      
          )
          :effect (and
              (not (at-opponent ?loc ?opp))                 
          )
      )
    )
    """
    domainDefensiveFile.write(domainContent)
    domainDefensiveFile.close()
  def createDefensiveProblemFile(self, gameState):
    cellsCoordinate = gameState.getWalls().asList(False)
    agentsCoordinate = gameState.getAgentPosition(self.index)
    foodsCoordinate = self.getFood(gameState).asList()
    capsulesCoordinate = self.getCapsules(gameState)
    opponentsCoordinate = [gameState.getAgentPosition(i) for i in self.getOpponents(gameState)]

    cellsList = ['cell{}_{}'.format(t[0], t[1]) for t in cellsCoordinate]
    connections = []
    for cell in cellsCoordinate:
      if (cell[0]+1, cell[1]) in cellsCoordinate:
        connection = '(connected cell{}_{} cell{}_{})\n\t\t'.format(cell[0], cell[1], cell[0]+1, cell[1])
        connections.append(connection)
      if (cell[0], cell[1]+1) in cellsCoordinate:
        connection = '(connected cell{}_{} cell{}_{})\n\t\t'.format(cell[0], cell[1], cell[0], cell[1]+1)
        connections.append(connection)
      if (cell[0]-1, cell[1]) in cellsCoordinate:
        connection = '(connected cell{}_{} cell{}_{})\n\t\t'.format(cell[0], cell[1], cell[0]-1, cell[1])
        connections.append(connection)
      if (cell[0], cell[1]-1) in cellsCoordinate:
        connection = '(connected cell{}_{} cell{}_{})\n\t\t'.format(cell[0], cell[1], cell[0], cell[1]-1)
        connections.append(connection)
    foodsList = ['food{}'.format(i) for i in range(len(foodsCoordinate))]
    foods = ["(at-food cell{}_{} food{})\n\t\t".format(t[0], t[1], index) for index, t in enumerate(foodsCoordinate)]
    agent = '(at-agent cell{}_{})\n\t\t'.format(agentsCoordinate[0], agentsCoordinate[1])
    capsules = ['(has-capsule cell{}_{})\n\t\t'.format(capsule[0], capsule[1]) for capsule in capsulesCoordinate]
    opponents = [f"(at-opponent cell{opponent[0]}_{opponent[1]} opponent{index})\n\t\t" for index, opponent in enumerate(opponentsCoordinate) if opponent is not None]

    cells_str = '  '.join(cellsList) + ' - cells'
    foods_str = '  '.join(foodsList) + ' - foods'
    foods_location_str = ''.join(foods)
    connections_str = ''.join(connections)
    if opponents:
      opponents_str = ''.join(opponents)
    else:
      opponents_str = '\n'
    capsules_str = ''.join(capsules)
    goalStr = self.setDefensiveAgentGoal(gameState)
    problem_str = """
    (define (problem problem_defensive)
      (:domain defensiveAgent)
      (:objects
        {}
        opponent0, opponent1 - opponents
      )
      (:init
        {}
        {}
        {}
        {}
      )
      (:goal(and
        {}
      ))
    )       
    """.format(cells_str, agent, capsules_str, opponents_str, connections_str, goalStr)
    problem_file = open(f"{filePath}/problem_defensive.pddl", "w")
    problem_file.write(problem_str)
    problem_file.close()

  def setDefensiveAgentGoal(self, gameState):
    agentPosition = gameState.getAgentState(self.index).getPosition()
    mysideOpponents = self.getMysideOpponents(gameState)
    self.getPossiableOpponents(gameState)

    if mysideOpponents:
      return '(at-agent cell{}_{})\n\t\t'.format(mysideOpponents[0], mysideOpponents[1])
    elif self.oppList and self.oppList != agentPosition:
      return '(at-agent cell{}_{})\n\t\t'.format(self.oppList[0], self.oppList[1])
    else:
      self.oppList = None
      x, y = random.choice(sorted(self.foodsDistribution(gameState, 'def'), key=lambda group: len(group), reverse=True)[0])
      return '(at-agent cell{}_{})\n\t\t'.format(x, y)

  def problemSolver(self, gameState):
    (agentX, agentY) = gameState.getAgentState(self.index).getPosition()
    domain = f"{filePath}/domain_defensive.pddl"
    problem = f"{filePath}/problem_defensive.pddl"
    planner = FFPlaner(domain, problem)
    plannedAction = planner.getSolution()
    if plannedAction is not None:
      plannedX = int(plannedAction[0])
      plannedY = int(plannedAction[1])
      if plannedX == agentX - 1 and plannedY == agentY:
        return "West"
      elif plannedX == agentX and plannedY == agentY + 1:
        return "North"
      elif plannedX == agentX and plannedY == agentY - 1:
        return "South"
      elif plannedX == agentX + 1 and plannedY == agentY:
        return "East"
      else:
        return "Stop"
    else:
      return "Stop"

  def getPossiableOpponents(self, gameState):
    difference = []
    agentPosition = gameState.getAgentState(self.index).getPosition()
    preGameState = self.getPreviousObservation()
    if preGameState is not None:
      preFoods = self.getFoodYouAreDefending(preGameState).asList()
      currentFoods = self.getFoodYouAreDefending(gameState).asList()
      difference = list(set(preFoods) ^ set(currentFoods))
    if difference:
      self.oppList = min(difference, key=lambda pos: self.getMazeDistance(agentPosition, pos))
  def getMysideOpponents(self, gameState):
    mysideOpponents = []
    agentPosition = gameState.getAgentState(self.index).getPosition()
    opponents = self.getOpponents(gameState)
    for opponent in opponents:
      opponentPosition = gameState.getAgentPosition(opponent)
      if opponentPosition is not None:
        if (self.isRed and opponentPosition[0] <= self.middleLine) or (
                not self.isRed and opponentPosition[0] >= self.middleLine):
          mysideOpponents.append(opponentPosition)
          return min(mysideOpponents, key=lambda pos: self.getMazeDistance(agentPosition, pos))
    return mysideOpponents

  def chooseAction(self, gameState):
    self.createDefensiveDomianFile()
    self.createDefensiveProblemFile(gameState)
    return self.problemSolver(gameState)


class FFPlaner():
  def __init__(self, domain, problem):
    self.domain = domain
    self.problem = problem
  def call_ff(self):
    cmd = [ffPath, "-o", f"{self.domain}", "-f", f"{self.problem}"]
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    return result.stdout.splitlines() if result.returncode == 0 else None

  def parse_ff_output(self, lines):
    plan = []
    for line in lines:
      search_action = re.search(r'\d: (.*)$', line)
      if search_action:
        plan.append(search_action.group(1))

      # Empty Plan
      if line.find("ff: goal can be simplified to TRUE.") != -1:
        return []
      # No Plan
      if line.find("ff: goal can be simplified to FALSE.") != -1:
        return None

    if len(plan) > 0:
      return plan
    else:
      # print('should never have ocurred!')
      return None

  def getSolution(self):
    output = self.call_ff()
    if output is not None:
      plan = self.parse_ff_output(output)
      if plan is not None:
        solution = plan[0].split()[2]
        position = solution.replace('CELL', '').split('_')
        return position
    else:
      return None