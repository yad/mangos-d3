/*
 * This file is part of the CMaNGOS Project. See AUTHORS file for Copyright information
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#include "Creature.h"
#include "Database/DatabaseEnv.h"
#include "WorldPacket.h"
#include "World.h"
#include "ObjectMgr.h"
#include "ScriptMgr.h"
#include "ObjectGuid.h"
#include "SQLStorages.h"
#include "SpellMgr.h"
#include "QuestDef.h"
#include "GossipDef.h"
#include "Player.h"
#include "GameEventMgr.h"
#include "PoolManager.h"
#include "Opcodes.h"
#include "Log.h"
#include "LootMgr.h"
#include "MapManager.h"
#include "CreatureAI.h"
#include "CreatureAISelector.h"
#include "Formulas.h"
#include "WaypointMovementGenerator.h"
#include "InstanceData.h"
#include "MapPersistentStateMgr.h"
#include "BattleGround/BattleGroundMgr.h"
#include "OutdoorPvP/OutdoorPvP.h"
#include "Spell.h"
#include "Util.h"
#include "GridNotifiers.h"
#include "GridNotifiersImpl.h"
#include "CellImpl.h"
#include "movement/MoveSplineInit.h"
#include "CreatureLinkingMgr.h"

// apply implementation of the singletons
#include "Policies/Singleton.h"

ObjectGuid CreatureData::GetObjectGuid(uint32 lowguid) const
{
    // info existence checked at loading
    return ObjectMgr::GetCreatureTemplate(id)->GetObjectGuid(lowguid);
}

TrainerSpell const* TrainerSpellData::Find(uint32 spell_id) const
{
    TrainerSpellMap::const_iterator itr = spellList.find(spell_id);
    if (itr != spellList.end())
        return &itr->second;

    return nullptr;
}

bool VendorItemData::RemoveItem(uint32 item_id)
{
    bool found = false;
    for (VendorItemList::iterator i = m_items.begin(); i != m_items.end();)
    {
        // can have many examples
        if ((*i)->item == item_id)
        {
            i = m_items.erase(i);
            found = true;
        }
        else
            ++i;
    }

    return found;
}

VendorItem const* VendorItemData::FindItemCostPair(uint32 item_id, uint32 extendedCost) const
{
    for (VendorItemList::const_iterator i = m_items.begin(); i != m_items.end(); ++i)
    {
        // Skip checking for conditions, condition system is powerfull enough to not require additional entries only for the conditions
        if ((*i)->item == item_id && (*i)->ExtendedCost == extendedCost)
            return *i;
    }
    return nullptr;
}

bool ForcedDespawnDelayEvent::Execute(uint64 /*e_time*/, uint32 /*p_time*/)
{
    m_owner.ForcedDespawn();
    return true;
}

void CreatureCreatePos::SelectFinalPoint(Creature* cr)
{
    // if object provided then selected point at specific dist/angle from object forward look
    if (m_closeObject)
    {
        if (m_dist == 0.0f)
        {
            m_pos.x = m_closeObject->GetPositionX();
            m_pos.y = m_closeObject->GetPositionY();
            m_pos.z = m_closeObject->GetPositionZ();
        }
        else
            m_closeObject->GetClosePoint(m_pos.x, m_pos.y, m_pos.z, cr->GetObjectBoundingRadius(), m_dist, m_angle);
    }
}

bool CreatureCreatePos::Relocate(Creature* cr) const
{
    cr->Relocate(m_pos.x, m_pos.y, m_pos.z, m_pos.o);

    if (!cr->IsPositionValid())
    {
        sLog.outError("%s not created. Suggested coordinates isn't valid (X: %f Y: %f)", cr->GetGuidStr().c_str(), cr->GetPositionX(), cr->GetPositionY());
        return false;
    }

    return true;
}

Creature::Creature(CreatureSubtype subtype) : Unit(),
    i_AI(nullptr),
    m_lootMoney(0), m_lootGroupRecipientId(0),
    m_lootStatus(CREATURE_LOOT_STATUS_NONE),
    m_corpseDecayTimer(0), m_respawnTime(0), m_respawnDelay(25), m_corpseDelay(60), m_aggroDelay(0), m_respawnradius(5.0f),
    m_subtype(subtype), m_defaultMovementType(IDLE_MOTION_TYPE), m_equipmentId(0),
    m_AlreadyCallAssistance(false), m_AlreadySearchedAssistance(false),
    m_AI_locked(false), m_isDeadByDefault(false), m_temporaryFactionFlags(TEMPFACTION_NONE),
    m_meleeDamageSchoolMask(SPELL_SCHOOL_MASK_NORMAL), m_originalEntry(0),
    m_creatureInfo(nullptr)
{
    m_regenTimer = 200;
    m_valuesCount = UNIT_END;

    for (int i = 0; i < CREATURE_MAX_SPELLS; ++i)
        m_spells[i] = 0;

    m_CreatureSpellCooldowns.clear();
    m_CreatureCategoryCooldowns.clear();

    SetWalk(true, true);
}

Creature::~Creature()
{
    CleanupsBeforeDelete();

    m_vendorItemCounts.clear();

    delete i_AI;
    i_AI = nullptr;
}

bool Creature::IsPlayerSummon() const
{
    return this->GetOwner() && this->GetOwner()->GetTypeId() == TYPEID_PLAYER;
}

void Creature::AddToWorld()
{
    ///- Register the creature for guid lookup
    if (!IsInWorld() && GetObjectGuid().IsCreatureOrVehicle())
        GetMap()->GetObjectsStore().insert<Creature>(GetObjectGuid(), (Creature*)this);

    Unit::AddToWorld();

    // Make active if required
    std::set<uint32> const* mapList = sWorld.getConfigForceLoadMapIds();
    if ((mapList && mapList->find(GetMapId()) != mapList->end()) || (GetCreatureInfo()->ExtraFlags & CREATURE_FLAG_EXTRA_ACTIVE))
        SetActiveObjectState(true);

    SetEliteIfChosen();

    SummonCreaturePool();
}

void Creature::RemoveFromWorld()
{
    ///- Remove the creature from the accessor
    if (IsInWorld() && GetObjectGuid().IsCreatureOrVehicle())
        GetMap()->GetObjectsStore().erase<Creature>(GetObjectGuid(), (Creature*)nullptr);

    Unit::RemoveFromWorld();
}

void Creature::RemoveCorpse()
{
    // since pool system can fail to roll unspawned object, this one can remain spawned, so must set respawn nevertheless
    if (uint16 poolid = sPoolMgr.IsPartOfAPool<Creature>(GetGUIDLow()))
        sPoolMgr.UpdatePool<Creature>(*GetMap()->GetPersistentState(), poolid, GetGUIDLow());

    if (!IsInWorld())                                       // can be despawned by update pool
        return;

    if ((getDeathState() != CORPSE && !m_isDeadByDefault) || (getDeathState() != ALIVE && m_isDeadByDefault))
        return;

    DEBUG_FILTER_LOG(LOG_FILTER_AI_AND_MOVEGENSS, "Removing corpse of %s ", GetGuidStr().c_str());

    m_corpseDecayTimer = 0;
    SetDeathState(DEAD);
    UpdateObjectVisibility();

    delete loot;
    loot = nullptr;
    m_lootStatus = CREATURE_LOOT_STATUS_NONE;
    uint32 respawnDelay = 0;

    if (AI())
        AI()->CorpseRemoved(respawnDelay);

    if (m_isCreatureLinkingTrigger)
        GetMap()->GetCreatureLinkingHolder()->DoCreatureLinkingEvent(LINKING_EVENT_DESPAWN, this);

    if (InstanceData* mapInstance = GetInstanceData())
        mapInstance->OnCreatureDespawn(this);

    // script can set time (in seconds) explicit, override the original
    if (respawnDelay)
        m_respawnTime = time(nullptr) + respawnDelay;

    float x, y, z, o;
    GetRespawnCoord(x, y, z, &o);
    GetMap()->CreatureRelocation(this, x, y, z, o);

    // forced recreate creature object at clients
    UnitVisibility currentVis = GetVisibility();
    SetVisibility(VISIBILITY_REMOVE_CORPSE);
    UpdateObjectVisibility();
    SetVisibility(currentVis);                              // restore visibility state
    UpdateObjectVisibility();
}

/**
 * change the entry of creature until respawn
 */
bool Creature::InitEntry(uint32 Entry, CreatureData const* data /*=nullptr*/, GameEventCreatureData const* eventData /*=nullptr*/)
{
    // use game event entry if any instead default suggested
    if (eventData && eventData->entry_id)
        Entry = eventData->entry_id;

    CreatureInfo const* normalInfo = ObjectMgr::GetCreatureTemplate(Entry);
    if (!normalInfo)
    {
        sLog.outErrorDb("Creature::UpdateEntry creature entry %u does not exist.", Entry);
        return false;
    }

    CreatureInfo const* cinfo = normalInfo;
    for (Difficulty diff = GetMap()->GetDifficulty(); diff > REGULAR_DIFFICULTY; diff = GetPrevDifficulty(diff, GetMap()->IsRaid()))
    {
        // we already have valid Map pointer for current creature!
        if (normalInfo->DifficultyEntry[diff - 1])
        {
            cinfo = ObjectMgr::GetCreatureTemplate(normalInfo->DifficultyEntry[diff - 1]);
            if (cinfo)
                break;                                      // template found

            // check and reported at startup, so just ignore (restore normalInfo)
            cinfo = normalInfo;
        }
    }

    SetEntry(Entry);                                        // normal entry always
    m_creatureInfo = cinfo;                                 // map mode related always

    SetObjectScale(cinfo->Scale);

    // equal to player Race field, but creature does not have race
    SetByteValue(UNIT_FIELD_BYTES_0, 0, 0);

    // known valid are: CLASS_WARRIOR,CLASS_PALADIN,CLASS_ROGUE,CLASS_MAGE
    SetByteValue(UNIT_FIELD_BYTES_0, 1, uint8(cinfo->UnitClass));

    uint32 display_id = ChooseDisplayId(GetCreatureInfo(), data, eventData);
    if (!display_id)                                        // Cancel load if no display id
    {
        sLog.outErrorDb("Creature (Entry: %u) has no model defined in table `creature_template`, can't load.", Entry);
        return false;
    }

    CreatureModelInfo const* minfo = sObjectMgr.GetCreatureModelRandomGender(display_id);
    if (!minfo)                                             // Cancel load if no model defined
    {
        sLog.outErrorDb("Creature (Entry: %u) has no model info defined in table `creature_model_info`, can't load.", Entry);
        return false;
    }

    display_id = minfo->modelid;                            // it can be different (for another gender)

    SetNativeDisplayId(display_id);

    // normally the same as native, but some has exceptions (Spell::DoSummonTotem)
    SetDisplayId(display_id);

    SetByteValue(UNIT_FIELD_BYTES_0, 2, minfo->gender);

    // set PowerType based on unit class
    switch (cinfo->UnitClass)
    {
        case CLASS_WARRIOR:
            SetPowerType(POWER_RAGE);
            break;
        case CLASS_PALADIN:
        case CLASS_MAGE:
            SetPowerType(POWER_MANA);
            break;
        case CLASS_ROGUE:
            SetPowerType(POWER_ENERGY);
            break;
        default:
            sLog.outErrorDb("Creature (Entry: %u) has unhandled unit class. Power type will not be set!", Entry);
            break;
    }

    // Load creature equipment
    if (eventData && eventData->equipment_id)
    {
        LoadEquipment(eventData->equipment_id);             // use event equipment if any for active event
    }
    else if (!data || data->equipmentId == 0)
    {
        if (cinfo->EquipmentTemplateId == 0)
            LoadEquipment(normalInfo->EquipmentTemplateId); // use default from normal template if diff does not have any
        else
            LoadEquipment(cinfo->EquipmentTemplateId);      // else use from diff template
    }
    else if (data && data->equipmentId != -1)
    {
        // override, -1 means no equipment
        LoadEquipment(data->equipmentId);
    }

    SetName(normalInfo->Name);                              // at normal entry always

    SetFloatValue(UNIT_MOD_CAST_SPEED, 1.0f);

    // update speed for the new CreatureInfo base speed mods
    UpdateSpeed(MOVE_WALK, false);
    UpdateSpeed(MOVE_RUN,  false);

    SetLevitate(cinfo->InhabitType & INHABIT_AIR); // TODO: may not be correct to send opcode at this point (already handled by UPDATE_OBJECT createObject)

    // check if we need to add swimming movement. TODO: i thing movement flags should be computed automatically at each movement of creature so we need a sort of UpdateMovementFlags() method
    if (cinfo->InhabitType & INHABIT_WATER &&               // check inhabit type water
            !(cinfo->ExtraFlags & CREATURE_FLAG_EXTRA_WALK_IN_WATER) &&  // check if creature is forced to walk (crabs, giant,...)
            data &&                                         // check if there is data to get creature spawn pos
            GetMap()->GetTerrain()->IsSwimmable(data->posX, data->posY, data->posZ, minfo->bounding_radius))  // check if creature is in water and have enough space to swim
        m_movementInfo.AddMovementFlag(MOVEFLAG_SWIMMING);  // add swimming movement

    // checked at loading
    m_defaultMovementType = MovementGeneratorType(cinfo->MovementType);



    return true;
}

bool Creature::UpdateEntry(uint32 Entry, Team team, const CreatureData* data /*=nullptr*/, GameEventCreatureData const* eventData /*=nullptr*/, bool preserveHPAndPower /*=true*/)
{
    if (!InitEntry(Entry, data, eventData))
        return false;

    // creatures always have melee weapon ready if any
    SetSheath(SHEATH_STATE_MELEE);

    SelectLevel(GetCreatureInfo(), preserveHPAndPower ? GetHealthPercent() : 100.0f);

    if (team == HORDE)
        setFaction(GetCreatureInfo()->FactionHorde);
    else
        setFaction(GetCreatureInfo()->FactionAlliance);

    SetUInt32Value(UNIT_NPC_FLAGS, GetCreatureInfo()->NpcFlags);

    uint32 attackTimer = GetCreatureInfo()->MeleeBaseAttackTime;

    SetAttackTime(BASE_ATTACK,  attackTimer);
    SetAttackTime(OFF_ATTACK,   attackTimer - attackTimer / 4);
    SetAttackTime(RANGED_ATTACK, GetCreatureInfo()->RangedBaseAttackTime);

    uint32 unitFlags = GetCreatureInfo()->UnitFlags;

    // we may need to append or remove additional flags
    if (HasFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_IN_COMBAT))
        unitFlags |= UNIT_FLAG_IN_COMBAT;

    if (m_movementInfo.HasMovementFlag(MOVEFLAG_SWIMMING) && (GetCreatureInfo()->ExtraFlags & CREATURE_FLAG_EXTRA_HAVE_NO_SWIM_ANIMATION) == 0)
        unitFlags |= UNIT_FLAG_UNK_15;
    else
        unitFlags &= ~UNIT_FLAG_UNK_15;

    SetUInt32Value(UNIT_FIELD_FLAGS, unitFlags);

    // preserve all current dynamic flags if exist
    uint32 dynFlags = GetUInt32Value(UNIT_DYNAMIC_FLAGS);
    SetUInt32Value(UNIT_DYNAMIC_FLAGS, dynFlags ? dynFlags : GetCreatureInfo()->DynamicFlags);

    SetModifierValue(UNIT_MOD_ARMOR,             BASE_VALUE, float(GetCreatureInfo()->Armor));
    SetModifierValue(UNIT_MOD_RESISTANCE_HOLY,   BASE_VALUE, float(GetCreatureInfo()->ResistanceHoly));
    SetModifierValue(UNIT_MOD_RESISTANCE_FIRE,   BASE_VALUE, float(GetCreatureInfo()->ResistanceFire));
    SetModifierValue(UNIT_MOD_RESISTANCE_NATURE, BASE_VALUE, float(GetCreatureInfo()->ResistanceNature));
    SetModifierValue(UNIT_MOD_RESISTANCE_FROST,  BASE_VALUE, float(GetCreatureInfo()->ResistanceFrost));
    SetModifierValue(UNIT_MOD_RESISTANCE_SHADOW, BASE_VALUE, float(GetCreatureInfo()->ResistanceShadow));
    SetModifierValue(UNIT_MOD_RESISTANCE_ARCANE, BASE_VALUE, float(GetCreatureInfo()->ResistanceArcane));

    SetCanModifyStats(true);
    UpdateAllStats();

    // checked and error show at loading templates
    if (FactionTemplateEntry const* factionTemplate = sFactionTemplateStore.LookupEntry(GetCreatureInfo()->FactionAlliance))
    {
        if (factionTemplate->factionFlags & FACTION_TEMPLATE_FLAG_PVP)
            SetPvP(true);
        else
            SetPvP(false);
    }

    // Try difficulty dependend version before falling back to base entry
    CreatureTemplateSpells const* templateSpells = sCreatureTemplateSpellsStorage.LookupEntry<CreatureTemplateSpells>(GetCreatureInfo()->Entry);
    if (!templateSpells)
        templateSpells = sCreatureTemplateSpellsStorage.LookupEntry<CreatureTemplateSpells>(GetEntry());
    if (templateSpells)
        for (int i = 0; i < CREATURE_MAX_SPELLS; ++i)
            m_spells[i] = templateSpells->spells[i];

    SetVehicleId(GetCreatureInfo()->VehicleTemplateId, 0);

    // if eventData set then event active and need apply spell_start
    if (eventData)
        ApplyGameEventSpells(eventData, true);

    return true;
}

uint32 Creature::ChooseDisplayId(const CreatureInfo* cinfo, const CreatureData* data /*= nullptr*/, GameEventCreatureData const* eventData /*=nullptr*/)
{
    // Use creature event model explicit, override any other static models
    if (eventData && eventData->modelid)
        return eventData->modelid;

    // Use creature model explicit, override template (creature.modelid)
    if (data && data->modelid_override)
        return data->modelid_override;

    // use defaults from the template
    uint32 display_id = 0;

    // models may be categorized as (in this order):
    // if mod4 && mod3 && mod2 && mod1  use any, by 25%-chance (other gender is selected and replaced after this function)
    // if mod3 && mod2 && mod1          use mod3 unless mod2 has modelid_alt_model (then all by 33%-chance)
    // if mod2                          use mod2 unless mod2 has modelid_alt_model (then both by 50%-chance)
    // if mod1                          use mod1

    // The follow decision tree needs to be updated if MAX_CREATURE_MODEL is changed.
    static_assert(MAX_CREATURE_MODEL == 4, "Need to update model selection code for new or removed model fields");

    // model selected here may be replaced with other_gender using own function
    if (cinfo->ModelId[3] && cinfo->ModelId[2] && cinfo->ModelId[1] && cinfo->ModelId[0])
    {
        display_id = cinfo->ModelId[urand(0, 3)];
    }
    else if (cinfo->ModelId[2] && cinfo->ModelId[1] && cinfo->ModelId[0])
    {
        uint32 modelid_tmp = sObjectMgr.GetCreatureModelAlternativeModel(cinfo->ModelId[1]);
        display_id = modelid_tmp ? cinfo->ModelId[urand(0, 2)] : cinfo->ModelId[2];
    }
    else if (cinfo->ModelId[1])
    {
        // We use this to eliminate invisible models vs. "dummy" models (infernals, etc).
        // Where it's expected to select one of two, model must have a alternative model defined (alternative model is normally the same as defined in ModelId1).
        // Same pattern is used in the above model selection, but the result may be ModelId3 and not ModelId2 as here.
        uint32 modelid_tmp = sObjectMgr.GetCreatureModelAlternativeModel(cinfo->ModelId[1]);
        display_id = modelid_tmp ? cinfo->ModelId[urand(0, 1)] : cinfo->ModelId[1];
    }
    else if (cinfo->ModelId[0])
    {
        display_id = cinfo->ModelId[0];
    }

    // fail safe, we use creature entry 1 and make error
    if (!display_id)
    {
        sLog.outErrorDb("Call customer support, ChooseDisplayId can not select native model for creature entry %u, model from creature entry 1 will be used instead.", cinfo->Entry);

        if (const CreatureInfo* creatureDefault = ObjectMgr::GetCreatureTemplate(1))
            display_id = creatureDefault->ModelId[0];
    }

    return display_id;
}

void Creature::Update(uint32 update_diff, uint32 diff)
{
    switch (m_deathState)
    {
        case JUST_ALIVED:
            // Don't must be called, see Creature::SetDeathState JUST_ALIVED -> ALIVE promoting.
            sLog.outError("Creature (GUIDLow: %u Entry: %u ) in wrong state: JUST_ALIVED (4)", GetGUIDLow(), GetEntry());
            break;
        case JUST_DIED:
            // Don't must be called, see Creature::SetDeathState JUST_DIED -> CORPSE promoting.
            sLog.outError("Creature (GUIDLow: %u Entry: %u ) in wrong state: JUST_DEAD (1)", GetGUIDLow(), GetEntry());
            break;
        case DEAD:
        {
            if (!IsPlayerSummon())
            {
                break;
            }

            if (m_respawnTime <= time(nullptr) && (!m_isSpawningLinked || GetMap()->GetCreatureLinkingHolder()->CanSpawn(this)))
            {
                DEBUG_FILTER_LOG(LOG_FILTER_AI_AND_MOVEGENSS, "Respawning...");
                m_respawnTime = 0;
                m_aggroDelay = sWorld.getConfig(CONFIG_UINT32_CREATURE_RESPAWN_AGGRO_DELAY);
                delete loot;
                loot = nullptr;

                // Clear possible auras having IsDeathPersistent() attribute
                RemoveAllAuras();

                if (m_originalEntry != GetEntry())
                {
                    // need preserver gameevent state
                    GameEventCreatureData const* eventData = sGameEventMgr.GetCreatureUpdateDataForActiveEvent(GetGUIDLow());
                    UpdateEntry(m_originalEntry, TEAM_NONE, nullptr, eventData);
                }

                CreatureInfo const* cinfo = GetCreatureInfo();

                SelectLevel(cinfo);
                UpdateAllStats();  // to be sure stats is correct regarding level of the creature
                SetUInt32Value(UNIT_DYNAMIC_FLAGS, UNIT_DYNFLAG_NONE);
                if (m_isDeadByDefault)
                {
                    SetDeathState(JUST_DIED);
                    SetHealth(0);
                    i_motionMaster.Clear();
                    clearUnitState(UNIT_STAT_ALL_STATE);
                    LoadCreatureAddon(true);
                }
                else
                    SetDeathState(JUST_ALIVED);

                // Call AI respawn virtual function
                if (AI())
                    AI()->JustRespawned();

                if (m_isCreatureLinkingTrigger)
                    GetMap()->GetCreatureLinkingHolder()->DoCreatureLinkingEvent(LINKING_EVENT_RESPAWN, this);

                GetMap()->Add(this);
            }
            break;
        }
        case CORPSE:
        {
            Unit::Update(update_diff, diff);
            if (loot)
                loot->Update();

            if (m_isDeadByDefault)
                break;

            if (m_corpseDecayTimer <= update_diff && IsPlayerSummon())
            {
                RemoveCorpse();
                break;
            }
            else
                m_corpseDecayTimer -= update_diff;

            break;
        }
        case ALIVE:
        {
            if (m_aggroDelay <= update_diff)
                m_aggroDelay = 0;
            else
                m_aggroDelay -= update_diff;

            if (m_isDeadByDefault)
            {
                if (m_corpseDecayTimer <= update_diff && IsPlayerSummon())
                {
                    RemoveCorpse();
                    break;
                }
                else
                    m_corpseDecayTimer -= update_diff;
            }

            Unit::Update(update_diff, diff);

            // creature can be dead after Unit::Update call
            // CORPSE/DEAD state will processed at next tick (in other case death timer will be updated unexpectedly)
            if (!isAlive())
                break;

            if (!IsInEvadeMode())
            {
                if (AI())
                {
                    // do not allow the AI to be changed during update
                    m_AI_locked = true;
                    AI()->UpdateAI(diff);   // AI not react good at real update delays (while freeze in non-active part of map)
                    m_AI_locked = false;
                }
            }

            // creature can be dead after UpdateAI call
            // CORPSE/DEAD state will processed at next tick (in other case death timer will be updated unexpectedly)
            if (!isAlive())
                break;

            RegenerateAll(update_diff);

            this->SetStatsBasedOnPlayerMaxLevel();
            break;
        }
        default:
            break;
    }
}

void Creature::RegenerateAll(uint32 update_diff)
{
    if (m_regenTimer > 0)
    {
        if (update_diff >= m_regenTimer)
            m_regenTimer = 0;
        else
            m_regenTimer -= update_diff;
    }
    if (m_regenTimer != 0)
        return;

    if (!isInCombat() || IsPolymorphed())
        RegenerateHealth();

    RegeneratePower();

    m_regenTimer = REGEN_TIME_FULL;
}

void Creature::RegeneratePower()
{
    if (!IsRegeneratingPower())
        return;

    Powers powerType = GetPowerType();
    uint32 curValue = GetPower(powerType);
    uint32 maxValue = GetMaxPower(powerType);

    if (curValue >= maxValue)
        return;

    float addValue = 0.0f;

    switch (powerType)
    {
        case POWER_MANA:
            // Combat and any controlled creature
            if (isInCombat() || GetCharmerOrOwnerGuid())
            {
                if (!IsUnderLastManaUseEffect())
                {
                    float ManaIncreaseRate = sWorld.getConfig(CONFIG_FLOAT_RATE_POWER_MANA);
                    float Spirit = GetStat(STAT_SPIRIT);

                    addValue = (Spirit / 5.0f + 17.0f) * ManaIncreaseRate;
                }
            }
            else
                addValue = maxValue / 3.0f;
            break;
        case POWER_ENERGY:
            // ToDo: for vehicle this is different - NEEDS TO BE FIXED!
            addValue = 20 * sWorld.getConfig(CONFIG_FLOAT_RATE_POWER_ENERGY);
            break;
        case POWER_FOCUS:
            addValue = 24 * sWorld.getConfig(CONFIG_FLOAT_RATE_POWER_FOCUS);
            break;
        default:
            return;
    }

    // Apply modifiers (if any)
    AuraList const& ModPowerRegenAuras = GetAurasByType(SPELL_AURA_MOD_POWER_REGEN);
    for (AuraList::const_iterator i = ModPowerRegenAuras.begin(); i != ModPowerRegenAuras.end(); ++i)
    {
        Modifier const* modifier = (*i)->GetModifier();
        if (modifier->m_miscvalue == int32(powerType))
            addValue += modifier->m_amount;
    }

    AuraList const& ModPowerRegenPCTAuras = GetAurasByType(SPELL_AURA_MOD_POWER_REGEN_PERCENT);
    for (AuraList::const_iterator i = ModPowerRegenPCTAuras.begin(); i != ModPowerRegenPCTAuras.end(); ++i)
    {
        Modifier const* modifier = (*i)->GetModifier();
        if (modifier->m_miscvalue == int32(powerType))
            addValue *= (modifier->m_amount + 100) / 100.0f;
    }

    ModifyPower(powerType, int32(addValue));
}

void Creature::RegenerateHealth()
{
    if (!IsRegeneratingHealth())
        return;

    uint32 curValue = GetHealth();
    uint32 maxValue = GetMaxHealth();

    if (curValue >= maxValue)
        return;

    uint32 addvalue = 0;

    // Not only pet, but any controlled creature
    if (GetCharmerOrOwnerGuid())
    {
        float HealthIncreaseRate = sWorld.getConfig(CONFIG_FLOAT_RATE_HEALTH);
        float Spirit = GetStat(STAT_SPIRIT);

        if (GetPower(POWER_MANA) > 0)
            addvalue = uint32(Spirit * 0.25 * HealthIncreaseRate);
        else
            addvalue = uint32(Spirit * 0.80 * HealthIncreaseRate);
    }
    else
        addvalue = maxValue / 3;

    ModifyHealth(addvalue);
}

void Creature::DoFleeToGetAssistance()
{
    if (!getVictim())
        return;

    float radius = sWorld.getConfig(CONFIG_FLOAT_CREATURE_FAMILY_FLEE_ASSISTANCE_RADIUS);
    if (radius > 0)
    {
        Creature* pCreature = nullptr;

        MaNGOS::NearestAssistCreatureInCreatureRangeCheck u_check(this, getVictim(), radius);
        MaNGOS::CreatureLastSearcher<MaNGOS::NearestAssistCreatureInCreatureRangeCheck> searcher(pCreature, u_check);
        Cell::VisitGridObjects(this, searcher, radius);

        SetNoSearchAssistance(true);
        UpdateSpeed(MOVE_RUN, false);

        if (!pCreature)
            SetFeared(true, getVictim()->GetObjectGuid(), 0 , sWorld.getConfig(CONFIG_UINT32_CREATURE_FAMILY_FLEE_DELAY));
        else
        {
            SetTargetGuid(ObjectGuid());        // creature flee loose its target
            GetMotionMaster()->MoveSeekAssistance(pCreature->GetPositionX(), pCreature->GetPositionY(), pCreature->GetPositionZ());
        }
    }
}

bool Creature::AIM_Initialize()
{
    // make sure nothing can change the AI during AI update
    if (m_AI_locked)
    {
        DEBUG_FILTER_LOG(LOG_FILTER_AI_AND_MOVEGENSS, "AIM_Initialize: failed to init, locked.");
        return false;
    }

    CreatureAI* oldAI = i_AI;
    i_motionMaster.Initialize();
    i_AI = FactorySelector::selectAI(this);
    delete oldAI;
    return true;
}

bool Creature::Create(uint32 guidlow, CreatureCreatePos& cPos, CreatureInfo const* cinfo, Team team /*= TEAM_NONE*/, const CreatureData* data /*= nullptr*/, GameEventCreatureData const* eventData /*= nullptr*/)
{
    SetMap(cPos.GetMap());
    SetPhaseMask(cPos.GetPhaseMask(), false);

    if (!CreateFromProto(guidlow, cinfo, team, data, eventData))
        return false;

    cPos.SelectFinalPoint(this);

    if (!cPos.Relocate(this))
        return false;

    // Notify the outdoor pvp script
    if (OutdoorPvP* outdoorPvP = sOutdoorPvPMgr.GetScript(GetZoneId()))
        outdoorPvP->HandleCreatureCreate(this);

    // Notify the map's instance data.
    // Only works if you create the object in it, not if it is moves to that map.
    // Normally non-players do not teleport to other maps.
    if (InstanceData* iData = GetMap()->GetInstanceData())
        iData->OnCreatureCreate(this);

    switch (GetCreatureInfo()->Rank)
    {
        case CREATURE_ELITE_RARE:
            m_corpseDelay = sWorld.getConfig(CONFIG_UINT32_CORPSE_DECAY_RARE);
            break;
        case CREATURE_ELITE_ELITE:
            m_corpseDelay = sWorld.getConfig(CONFIG_UINT32_CORPSE_DECAY_ELITE);
            break;
        case CREATURE_ELITE_RAREELITE:
            m_corpseDelay = sWorld.getConfig(CONFIG_UINT32_CORPSE_DECAY_RAREELITE);
            break;
        case CREATURE_ELITE_WORLDBOSS:
            m_corpseDelay = sWorld.getConfig(CONFIG_UINT32_CORPSE_DECAY_WORLDBOSS);
            break;
        default:
            m_corpseDelay = sWorld.getConfig(CONFIG_UINT32_CORPSE_DECAY_NORMAL);
            break;
    }

    // Add to CreatureLinkingHolder if needed
    if (sCreatureLinkingMgr.GetLinkedTriggerInformation(this))
        cPos.GetMap()->GetCreatureLinkingHolder()->AddSlaveToHolder(this);
    if (sCreatureLinkingMgr.IsLinkedEventTrigger(this))
    {
        m_isCreatureLinkingTrigger = true;
        cPos.GetMap()->GetCreatureLinkingHolder()->AddMasterToHolder(this);
    }

    LoadCreatureAddon(false);

    return true;
}

bool Creature::IsTrainerOf(Player* pPlayer, bool msg) const
{
    if (!isTrainer())
        return false;

    // pet trainers not have spells in fact now
    if (GetCreatureInfo()->TrainerType != TRAINER_TYPE_PETS)
    {
        TrainerSpellData const* cSpells = GetTrainerSpells();
        TrainerSpellData const* tSpells = GetTrainerTemplateSpells();

        // for not pet trainer expected not empty trainer list always
        if ((!cSpells || cSpells->spellList.empty()) && (!tSpells || tSpells->spellList.empty()))
        {
            sLog.outErrorDb("Creature %u (Entry: %u) have UNIT_NPC_FLAG_TRAINER but have empty trainer spell list.",
                            GetGUIDLow(), GetEntry());
            return false;
        }
    }

    switch (GetCreatureInfo()->TrainerType)
    {
        case TRAINER_TYPE_CLASS:
            if (pPlayer->getClass() != GetCreatureInfo()->TrainerClass)
            {
                if (msg)
                {
                    pPlayer->PlayerTalkClass->ClearMenus();
                    switch (GetCreatureInfo()->TrainerClass)
                    {
                        case CLASS_DRUID:  pPlayer->PlayerTalkClass->SendGossipMenu(4913, GetObjectGuid()); break;
                        case CLASS_HUNTER: pPlayer->PlayerTalkClass->SendGossipMenu(10090, GetObjectGuid()); break;
                        case CLASS_MAGE:   pPlayer->PlayerTalkClass->SendGossipMenu(328, GetObjectGuid()); break;
                        case CLASS_PALADIN: pPlayer->PlayerTalkClass->SendGossipMenu(1635, GetObjectGuid()); break;
                        case CLASS_PRIEST: pPlayer->PlayerTalkClass->SendGossipMenu(4436, GetObjectGuid()); break;
                        case CLASS_ROGUE:  pPlayer->PlayerTalkClass->SendGossipMenu(4797, GetObjectGuid()); break;
                        case CLASS_SHAMAN: pPlayer->PlayerTalkClass->SendGossipMenu(5003, GetObjectGuid()); break;
                        case CLASS_WARLOCK: pPlayer->PlayerTalkClass->SendGossipMenu(5836, GetObjectGuid()); break;
                        case CLASS_WARRIOR: pPlayer->PlayerTalkClass->SendGossipMenu(4985, GetObjectGuid()); break;
                    }
                }
                return false;
            }
            break;
        case TRAINER_TYPE_PETS:
            if (pPlayer->getClass() != CLASS_HUNTER)
            {
                if (msg)
                {
                    pPlayer->PlayerTalkClass->ClearMenus();
                    pPlayer->PlayerTalkClass->SendGossipMenu(3620, GetObjectGuid());
                }
                return false;
            }
            break;
        case TRAINER_TYPE_MOUNTS:
            if (GetCreatureInfo()->TrainerRace && pPlayer->getRace() != GetCreatureInfo()->TrainerRace)
            {
                // Allowed to train if exalted
                if (FactionTemplateEntry const* faction_template = getFactionTemplateEntry())
                {
                    if (pPlayer->GetReputationRank(faction_template->faction) == REP_EXALTED)
                        return true;
                }

                if (msg)
                {
                    pPlayer->PlayerTalkClass->ClearMenus();
                    switch (GetCreatureInfo()->TrainerClass)
                    {
                        case RACE_DWARF:        pPlayer->PlayerTalkClass->SendGossipMenu(5865, GetObjectGuid()); break;
                        case RACE_GNOME:        pPlayer->PlayerTalkClass->SendGossipMenu(4881, GetObjectGuid()); break;
                        case RACE_HUMAN:        pPlayer->PlayerTalkClass->SendGossipMenu(5861, GetObjectGuid()); break;
                        case RACE_NIGHTELF:     pPlayer->PlayerTalkClass->SendGossipMenu(5862, GetObjectGuid()); break;
                        case RACE_ORC:          pPlayer->PlayerTalkClass->SendGossipMenu(5863, GetObjectGuid()); break;
                        case RACE_TAUREN:       pPlayer->PlayerTalkClass->SendGossipMenu(5864, GetObjectGuid()); break;
                        case RACE_TROLL:        pPlayer->PlayerTalkClass->SendGossipMenu(5816, GetObjectGuid()); break;
                        case RACE_UNDEAD:       pPlayer->PlayerTalkClass->SendGossipMenu(624, GetObjectGuid()); break;
                        case RACE_BLOODELF:     pPlayer->PlayerTalkClass->SendGossipMenu(5862, GetObjectGuid()); break;
                        case RACE_DRAENEI:      pPlayer->PlayerTalkClass->SendGossipMenu(5864, GetObjectGuid()); break;
                    }
                }
                return false;
            }
            break;
        case TRAINER_TYPE_TRADESKILLS:
            if (GetCreatureInfo()->TrainerSpell && !pPlayer->HasSpell(GetCreatureInfo()->TrainerSpell))
            {
                if (msg)
                {
                    pPlayer->PlayerTalkClass->ClearMenus();
                    pPlayer->PlayerTalkClass->SendGossipMenu(11031, GetObjectGuid());
                }
                return false;
            }
            break;
        default:
            return false;                                   // checked and error output at creature_template loading
    }
    return true;
}

bool Creature::CanInteractWithBattleMaster(Player* pPlayer, bool msg) const
{
    if (!isBattleMaster())
        return false;

    BattleGroundTypeId bgTypeId = sBattleGroundMgr.GetBattleMasterBG(GetEntry());
    if (bgTypeId == BATTLEGROUND_TYPE_NONE)
        return false;

    if (!msg)
        return pPlayer->GetBGAccessByLevel(bgTypeId);

    if (!pPlayer->GetBGAccessByLevel(bgTypeId))
    {
        pPlayer->PlayerTalkClass->ClearMenus();
        switch (bgTypeId)
        {
            case BATTLEGROUND_AV:  pPlayer->PlayerTalkClass->SendGossipMenu(7616, GetObjectGuid()); break;
            case BATTLEGROUND_WS:  pPlayer->PlayerTalkClass->SendGossipMenu(7599, GetObjectGuid()); break;
            case BATTLEGROUND_AB:  pPlayer->PlayerTalkClass->SendGossipMenu(7642, GetObjectGuid()); break;
            case BATTLEGROUND_EY:
            case BATTLEGROUND_NA:
            case BATTLEGROUND_BE:
            case BATTLEGROUND_AA:
            case BATTLEGROUND_RL:
            case BATTLEGROUND_SA:
            case BATTLEGROUND_DS:
            case BATTLEGROUND_RV: pPlayer->PlayerTalkClass->SendGossipMenu(10024, GetObjectGuid()); break;
            default: break;
        }
        return false;
    }
    return true;
}

bool Creature::CanTrainAndResetTalentsOf(Player* pPlayer) const
{
    return pPlayer->getLevel() >= 10
           && GetCreatureInfo()->TrainerType == TRAINER_TYPE_CLASS
           && pPlayer->getClass() == GetCreatureInfo()->TrainerClass;
}

void Creature::PrepareBodyLootState()
{
    // loot may already exist (pickpocket case)
    delete loot;
    loot = nullptr;

    Player* killer = GetLootRecipient();

    if (killer)
        loot = new Loot(killer, this, LOOT_CORPSE);

    uint32 corpseLootedDelay;
    if (sWorld.getConfig(CONFIG_FLOAT_RATE_CORPSE_DECAY_LOOTED) > 0.0f)
        corpseLootedDelay = (uint32)((m_corpseDelay * IN_MILLISECONDS) * sWorld.getConfig(CONFIG_FLOAT_RATE_CORPSE_DECAY_LOOTED));
    else
        corpseLootedDelay = (m_respawnDelay * IN_MILLISECONDS) / 3;

    // if m_respawnDelay is larger than default corpse delay always use corpseLootedDelay
    if (m_respawnDelay > m_corpseDelay)
    {
        m_corpseDecayTimer = corpseLootedDelay;
    }
    else
    {
        // if m_respawnDelay is relatively short and corpseDecayTimer is larger than corpseLootedDelay
        if (m_corpseDecayTimer > corpseLootedDelay)
            m_corpseDecayTimer = corpseLootedDelay;
    }
}

/**
 * Return original player who tap creature, it can be different from player/group allowed to loot so not use it for loot code
 */
Player* Creature::GetOriginalLootRecipient() const
{
    return m_lootRecipientGuid ? ObjectAccessor::FindPlayer(m_lootRecipientGuid) : nullptr;
}

/**
 * Return group if player tap creature as group member, independent is player after leave group or stil be group member
 */
Group* Creature::GetGroupLootRecipient() const
{
    // original recipient group if set and not disbanded
    return m_lootGroupRecipientId ? sObjectMgr.GetGroupById(m_lootGroupRecipientId) : nullptr;
}

/**
 * Return player who can loot tapped creature (member of group or single player)
 *
 * In case when original player tap creature as group member then group tap prefered.
 * This is for example important if player after tap leave group.
 * If group not exist or disbanded or player tap creature not as group member return player
 */
Player* Creature::GetLootRecipient() const
{
    // original recipient group if set and not disbanded
    Group* group = GetGroupLootRecipient();

    // original recipient player if online
    Player* player = GetOriginalLootRecipient();

    // if group not set or disbanded return original recipient player if any
    if (!group)
        return player;

    // group case

    // return player if it still be in original recipient group
    if (player && player->GetGroup() == group)
        return player;

    // find any in group
    for (GroupReference* itr = group->GetFirstMember(); itr != nullptr; itr = itr->next())
        if (Player* p = itr->getSource())
            return p;

    return nullptr;
}

/**
 * Set player and group (if player group member) who tap creature
 */
void Creature::SetLootRecipient(Unit* unit)
{
    // set the player whose group should receive the right
    // to loot the creature after it dies
    // should be set to nullptr after the loot disappears

    if (!unit)
    {
        m_lootRecipientGuid.Clear();
        m_lootGroupRecipientId = 0;
        ForceValuesUpdateAtIndex(UNIT_DYNAMIC_FLAGS);       // needed to be sure tapping status is updated
        return;
    }

    Player* player = unit->GetCharmerOrOwnerPlayerOrPlayerItself();
    if (!player)                                            // normal creature, no player involved
        return;

    // set player for non group case or if group will disbanded
    m_lootRecipientGuid = player->GetObjectGuid();

    // set group for group existing case including if player will leave group at loot time
    if (Group* group = player->GetGroup())
        m_lootGroupRecipientId = group->GetId();

    ForceValuesUpdateAtIndex(UNIT_DYNAMIC_FLAGS);           // needed to be sure tapping status is updated
}

void Creature::SaveToDB()
{
    // this should only be used when the creature has already been loaded
    // preferably after adding to map, because mapid may not be valid otherwise
    CreatureData const* data = sObjectMgr.GetCreatureData(GetGUIDLow());
    if (!data)
    {
        sLog.outError("Creature::SaveToDB failed, cannot get creature data!");
        return;
    }

    SaveToDB(GetMapId(), data->spawnMask, GetPhaseMask());
}

void Creature::SaveToDB(uint32 mapid, uint8 spawnMask, uint32 phaseMask)
{
    // update in loaded data
    CreatureData& data = sObjectMgr.NewOrExistCreatureData(GetGUIDLow());

    uint32 displayId = GetNativeDisplayId();

    // check if it's a custom model and if not, use 0 for displayId
    CreatureInfo const* cinfo = GetCreatureInfo();
    if (cinfo)
    {
        // The following if-else assumes that there are 4 model fields and needs updating if this is changed.
        static_assert(MAX_CREATURE_MODEL == 4, "Need to update custom model check for new/removed model fields.");

        if (displayId != cinfo->ModelId[0] && displayId != cinfo->ModelId[1] &&
                displayId != cinfo->ModelId[2] && displayId != cinfo->ModelId[3])
        {
            for (int i = 0; i < MAX_CREATURE_MODEL && displayId; ++i)
                if (cinfo->ModelId[i])
                    if (CreatureModelInfo const* minfo = sObjectMgr.GetCreatureModelInfo(cinfo->ModelId[i]))
                        if (displayId == minfo->modelid_other_gender)
                            displayId = 0;
        }
        else
            displayId = 0;
    }

    // data->guid = guid don't must be update at save
    data.id = GetEntry();
    data.mapid = mapid;
    data.spawnMask = spawnMask;
    data.phaseMask = phaseMask;
    data.modelid_override = displayId;
    data.equipmentId = GetEquipmentId();
    data.posX = GetPositionX();
    data.posY = GetPositionY();
    data.posZ = GetPositionZ();
    data.orientation = GetOrientation();
    data.spawntimesecs = m_respawnDelay;
    // prevent add data integrity problems
    data.spawndist = GetDefaultMovementType() == IDLE_MOTION_TYPE ? 0 : m_respawnradius;
    data.currentwaypoint = 0;
    data.curhealth = GetHealth();
    data.curmana = GetPower(POWER_MANA);
    data.is_dead = m_isDeadByDefault;
    // prevent add data integrity problems
    data.movementType = !m_respawnradius && GetDefaultMovementType() == RANDOM_MOTION_TYPE
                        ? IDLE_MOTION_TYPE : GetDefaultMovementType();

    // updated in DB
    WorldDatabase.BeginTransaction();

    WorldDatabase.PExecuteLog("DELETE FROM creature WHERE guid=%u", GetGUIDLow());

    std::ostringstream ss;
    ss << "INSERT INTO creature VALUES ("
       << GetGUIDLow() << ","
       << data.id << ","
       << data.mapid << ","
       << uint32(data.spawnMask) << ","                    // cast to prevent save as symbol
       << uint16(data.phaseMask) << ","                    // prevent out of range error
       << data.modelid_override << ","
       << data.equipmentId << ","
       << data.posX << ","
       << data.posY << ","
       << data.posZ << ","
       << data.orientation << ","
       << data.spawntimesecs << ","                        // respawn time
       << (float) data.spawndist << ","                    // spawn distance (float)
       << data.currentwaypoint << ","                      // currentwaypoint
       << data.curhealth << ","                            // curhealth
       << data.curmana << ","                              // curmana
       << (data.is_dead  ? 1 : 0) << ","                   // is_dead
       << uint32(data.movementType) << ")";                // default movement generator type, cast to prevent save as symbol

    WorldDatabase.PExecuteLog("%s", ss.str().c_str());

    WorldDatabase.CommitTransaction();
}

void Creature::SelectLevel(const CreatureInfo* cinfo, float percentHealth /*= 100.0f*/)
{
    uint32 rank = IsPet() ? 0 : cinfo->Rank;                // TODO :: IsPet probably not needed here

    // level
    uint32 const minlevel = cinfo->MinLevel;
    uint32 const maxlevel = cinfo->MaxLevel;
    uint32 level = minlevel == maxlevel ? minlevel : urand(minlevel, maxlevel);
    SetLevel(level);

    //////////////////////////////////////////////////////////////////////////
    // Calculate level dependend stats
    //////////////////////////////////////////////////////////////////////////

    uint32 health;
    uint32 mana;

    if (CreatureClassLvlStats const* cCLS = sObjectMgr.GetCreatureClassLvlStats(level, cinfo->UnitClass, cinfo->Expansion))
    {
        // Use Creature Stats to calculate stat values

        // health
        health = cCLS->BaseHealth * cinfo->HealthMultiplier;

        // mana
        mana = cCLS->BaseMana * cinfo->PowerMultiplier;
    }
    else
    {
        // Use old style to calculate stat values
        float rellevel = maxlevel == minlevel ? 0 : (float(level - minlevel)) / (maxlevel - minlevel);

        // health
        uint32 minhealth = std::min(cinfo->MaxLevelHealth, cinfo->MinLevelHealth);
        uint32 maxhealth = std::max(cinfo->MaxLevelHealth, cinfo->MinLevelHealth);
        health = uint32(minhealth + uint32(rellevel * (maxhealth - minhealth)));

        // mana
        uint32 minmana = std::min(cinfo->MaxLevelMana, cinfo->MinLevelMana);
        uint32 maxmana = std::max(cinfo->MaxLevelMana, cinfo->MinLevelMana);
        mana = minmana + uint32(rellevel * (maxmana - minmana));
    }

    health *= _GetHealthMod(rank); // Apply custom config settting
    if (health < 1)
        health = 1;

    //////////////////////////////////////////////////////////////////////////
    // Set values
    //////////////////////////////////////////////////////////////////////////

    // health
    SetCreateHealth(health);
    SetMaxHealth(health);

    if (percentHealth == 100.0f)
        SetHealth(health);
    else
        SetHealthPercent(percentHealth);

    SetModifierValue(UNIT_MOD_HEALTH, BASE_VALUE, float(health));

    // all power types
    for (int i = POWER_MANA; i <= POWER_RUNIC_POWER; ++i)
    {
        uint32 maxValue;

        switch (i)
        {
            case POWER_MANA:        maxValue = mana; break;
            case POWER_RAGE:        maxValue = 0; break;
            case POWER_FOCUS:       maxValue = POWER_FOCUS_DEFAULT; break;
            case POWER_ENERGY:      maxValue = POWER_ENERGY_DEFAULT * cinfo->PowerMultiplier; break;
            case POWER_HAPPINESS:   maxValue = POWER_HAPPINESS_DEFAULT; break;
            case POWER_RUNE:        maxValue = 0; break;
            case POWER_RUNIC_POWER: maxValue = 0; break;
        }

        uint32 value = maxValue;

        // For non regenerating powers set 0
        if ((i == POWER_ENERGY || i == POWER_MANA) && !IsRegeneratingPower())
            value = 0;

        // Mana requires an extra field to be set
        if (i == POWER_MANA)
            SetCreateMana(value);

        SetMaxPower(Powers(i), maxValue);
        SetPower(Powers(i), value);
        SetModifierValue(UnitMods(UNIT_MOD_POWER_START + i), BASE_VALUE, float(value));
    }

    // damage
    float damagemod = _GetDamageMod(rank);

    SetBaseWeaponDamage(BASE_ATTACK, MINDAMAGE, cinfo->MinMeleeDmg * damagemod);
    SetBaseWeaponDamage(BASE_ATTACK, MAXDAMAGE, cinfo->MaxMeleeDmg * damagemod);

    SetBaseWeaponDamage(OFF_ATTACK, MINDAMAGE, cinfo->MinMeleeDmg * damagemod);
    SetBaseWeaponDamage(OFF_ATTACK, MAXDAMAGE, cinfo->MaxMeleeDmg * damagemod);

    SetFloatValue(UNIT_FIELD_MINRANGEDDAMAGE, cinfo->MinRangedDmg * damagemod);
    SetFloatValue(UNIT_FIELD_MAXRANGEDDAMAGE, cinfo->MaxRangedDmg * damagemod);

    SetModifierValue(UNIT_MOD_ATTACK_POWER, BASE_VALUE, cinfo->MeleeAttackPower * damagemod);
}

float Creature::_GetHealthMod(int32 Rank)
{
    switch (Rank)                                           // define rates for each elite rank
    {
        case CREATURE_ELITE_NORMAL:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_NORMAL_HP);
        case CREATURE_ELITE_ELITE:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_ELITE_HP);
        case CREATURE_ELITE_RAREELITE:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_RAREELITE_HP);
        case CREATURE_ELITE_WORLDBOSS:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_WORLDBOSS_HP);
        case CREATURE_ELITE_RARE:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_RARE_HP);
        default:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_ELITE_HP);
    }
}

float Creature::_GetDamageMod(int32 Rank)
{
    switch (Rank)                                           // define rates for each elite rank
    {
        case CREATURE_ELITE_NORMAL:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_NORMAL_DAMAGE);
        case CREATURE_ELITE_ELITE:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_ELITE_DAMAGE);
        case CREATURE_ELITE_RAREELITE:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_RAREELITE_DAMAGE);
        case CREATURE_ELITE_WORLDBOSS:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_WORLDBOSS_DAMAGE);
        case CREATURE_ELITE_RARE:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_RARE_DAMAGE);
        default:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_ELITE_DAMAGE);
    }
}

float Creature::_GetSpellDamageMod(int32 Rank)
{
    switch (Rank)                                           // define rates for each elite rank
    {
        case CREATURE_ELITE_NORMAL:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_NORMAL_SPELLDAMAGE);
        case CREATURE_ELITE_ELITE:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_ELITE_SPELLDAMAGE);
        case CREATURE_ELITE_RAREELITE:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_RAREELITE_SPELLDAMAGE);
        case CREATURE_ELITE_WORLDBOSS:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_WORLDBOSS_SPELLDAMAGE);
        case CREATURE_ELITE_RARE:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_RARE_SPELLDAMAGE);
        default:
            return sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_ELITE_ELITE_SPELLDAMAGE);
    }
}

bool Creature::CreateFromProto(uint32 guidlow, CreatureInfo const* cinfo, Team team, const CreatureData* data /*=nullptr*/, GameEventCreatureData const* eventData /*=nullptr*/)
{
    m_originalEntry = cinfo->Entry;

    Object::_Create(guidlow, cinfo->Entry, cinfo->GetHighGuid());

    if (!UpdateEntry(cinfo->Entry, team, data, eventData, false))
        return false;

    return true;
}

bool Creature::LoadFromDB(uint32 guidlow, Map* map)
{
    CreatureData const* data = sObjectMgr.GetCreatureData(guidlow);

    if (!data)
    {
        sLog.outErrorDb("Creature (GUID: %u) not found in table `creature`, can't load. ", guidlow);
        return false;
    }

    CreatureInfo const* cinfo = ObjectMgr::GetCreatureTemplate(data->id);
    if (!cinfo)
    {
        sLog.outErrorDb("Creature (Entry: %u) not found in table `creature_template`, can't load. ", data->id);
        return false;
    }

    GameEventCreatureData const* eventData = sGameEventMgr.GetCreatureUpdateDataForActiveEvent(guidlow);

    // Creature can be loaded already in map if grid has been unloaded while creature walk to another grid
    if (map->GetCreature(cinfo->GetObjectGuid(guidlow)))
        return false;

    CreatureCreatePos pos(map, data->posX, data->posY, data->posZ, data->orientation, data->phaseMask);

    if (!Create(guidlow, pos, cinfo, TEAM_NONE, data, eventData))
        return false;

    SetRespawnCoord(pos);
    m_respawnradius = data->spawndist;

    m_respawnDelay = data->spawntimesecs;
    m_corpseDelay = std::min(m_respawnDelay * 9 / 10, m_corpseDelay); // set corpse delay to 90% of the respawn delay
    m_isDeadByDefault = data->is_dead;
    m_deathState = m_isDeadByDefault ? DEAD : ALIVE;

    m_respawnTime  = map->GetPersistentState()->GetCreatureRespawnTime(GetGUIDLow());

    if (m_respawnTime > time(nullptr))                         // not ready to respawn
    {
        m_deathState = DEAD;
        if (CanFly())
        {
            float tz = GetTerrain()->GetHeightStatic(data->posX, data->posY, data->posZ, false);
            if (data->posZ - tz > 0.1)
                Relocate(data->posX, data->posY, tz);
        }
    }
    else if (m_respawnTime)                                 // respawn time set but expired
    {
        m_respawnTime = 0;

        GetMap()->GetPersistentState()->SaveCreatureRespawnTime(GetGUIDLow(), 0);
    }

    uint32 curhealth = data->curhealth;
    if (curhealth)
    {
        curhealth = uint32(curhealth * _GetHealthMod(GetCreatureInfo()->Rank));
        if (curhealth < 1)
            curhealth = 1;
    }

    if (sCreatureLinkingMgr.IsSpawnedByLinkedMob(this))
    {
        m_isSpawningLinked = true;
        if (m_deathState == ALIVE && !GetMap()->GetCreatureLinkingHolder()->CanSpawn(this))
        {
            m_deathState = DEAD;

            // Just set to dead, so need to relocate like above
            if (CanFly())
            {
                float tz = GetTerrain()->GetHeightStatic(data->posX, data->posY, data->posZ, false);
                if (data->posZ - tz > 0.1)
                    Relocate(data->posX, data->posY, tz);
            }
        }
    }

    SetHealth(m_deathState == ALIVE ? curhealth : 0);
    SetPower(POWER_MANA, data->curmana);

    SetMeleeDamageSchool(SpellSchools(GetCreatureInfo()->DamageSchool));

    // checked at creature_template loading
    m_defaultMovementType = MovementGeneratorType(data->movementType);

    AIM_Initialize();

    // Creature Linking, Initial load is handled like respawn
    if (m_isCreatureLinkingTrigger && isAlive())
        GetMap()->GetCreatureLinkingHolder()->DoCreatureLinkingEvent(LINKING_EVENT_RESPAWN, this);

    // check if it is rabbit day
    if (isAlive() && sWorld.getConfig(CONFIG_UINT32_RABBIT_DAY))
    {
        time_t rabbit_day = time_t(sWorld.getConfig(CONFIG_UINT32_RABBIT_DAY));
        tm rabbit_day_tm = *localtime(&rabbit_day);
        tm now_tm = *localtime(&sWorld.GetGameTime());

        if (now_tm.tm_mon == rabbit_day_tm.tm_mon && now_tm.tm_mday == rabbit_day_tm.tm_mday)
            CastSpell(this, 10710 + urand(0, 2), true);
    }

    return true;
}

void Creature::LoadEquipment(uint32 equip_entry, bool force)
{
    if (equip_entry == 0)
    {
        if (force)
        {
            for (uint8 i = 0; i < MAX_VIRTUAL_ITEM_SLOT; ++i)
                SetVirtualItem(VirtualItemSlot(i), 0);
            m_equipmentId = 0;
        }
        return;
    }

    EquipmentInfo const* einfo = sObjectMgr.GetEquipmentInfo(equip_entry);
    if (!einfo)
        return;

    m_equipmentId = equip_entry;
    for (uint8 i = 0; i < MAX_VIRTUAL_ITEM_SLOT; ++i)
        SetVirtualItem(VirtualItemSlot(i), einfo->equipentry[i]);
}

bool Creature::HasQuest(uint32 quest_id) const
{
    QuestRelationsMapBounds bounds = sObjectMgr.GetCreatureQuestRelationsMapBounds(GetEntry());
    for (QuestRelationsMap::const_iterator itr = bounds.first; itr != bounds.second; ++itr)
    {
        if (itr->second == quest_id)
            return true;
    }
    return false;
}

bool Creature::HasInvolvedQuest(uint32 quest_id) const
{
    QuestRelationsMapBounds bounds = sObjectMgr.GetCreatureQuestInvolvedRelationsMapBounds(GetEntry());
    for (QuestRelationsMap::const_iterator itr = bounds.first; itr != bounds.second; ++itr)
    {
        if (itr->second == quest_id)
            return true;
    }
    return false;
}

struct CreatureRespawnDeleteWorker
{
    explicit CreatureRespawnDeleteWorker(uint32 guid) : i_guid(guid) {}

    void operator()(MapPersistentState* state)
    {
        state->SaveCreatureRespawnTime(i_guid, 0);
    }

    uint32 i_guid;
};

void Creature::DeleteFromDB()
{
    CreatureData const* data = sObjectMgr.GetCreatureData(GetGUIDLow());
    if (!data)
    {
        DEBUG_LOG("Trying to delete not saved creature!");
        return;
    }

    DeleteFromDB(GetGUIDLow(), data);
}

void Creature::DeleteFromDB(uint32 lowguid, CreatureData const* data)
{
    CreatureRespawnDeleteWorker worker(lowguid);
    sMapPersistentStateMgr.DoForAllStatesWithMapId(data->mapid, worker);

    sObjectMgr.DeleteCreatureData(lowguid);

    WorldDatabase.BeginTransaction();
    WorldDatabase.PExecuteLog("DELETE FROM creature WHERE guid=%u", lowguid);
    WorldDatabase.PExecuteLog("DELETE FROM creature_addon WHERE guid=%u", lowguid);
    WorldDatabase.PExecuteLog("DELETE FROM creature_movement WHERE id=%u", lowguid);
    WorldDatabase.PExecuteLog("DELETE FROM game_event_creature WHERE guid=%u", lowguid);
    WorldDatabase.PExecuteLog("DELETE FROM game_event_creature_data WHERE guid=%u", lowguid);
    WorldDatabase.PExecuteLog("DELETE FROM creature_battleground WHERE guid=%u", lowguid);
    WorldDatabase.PExecuteLog("DELETE FROM creature_linking WHERE guid=%u OR master_guid=%u", lowguid, lowguid);
    WorldDatabase.CommitTransaction();
}

float Creature::GetAttackDistance(Unit const* pl) const
{
    float aggroRate = sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_AGGRO);
    if (aggroRate == 0)
        return 0.0f;

    uint32 playerlevel   = pl->GetLevelForTarget(this);
    uint32 creaturelevel = GetLevelForTarget(pl);

    int32 leveldif       = int32(playerlevel) - int32(creaturelevel);

    // "The maximum Aggro Radius has a cap of 25 levels under. Example: A level 30 char has the same Aggro Radius of a level 5 char on a level 60 mob."
    if (leveldif < - 25)
        leveldif = -25;

    // "The aggro radius of a mob having the same level as the player is roughly 20 yards"
    float RetDistance = 20;

    // "Aggro Radius varies with level difference at a rate of roughly 1 yard/level"
    // radius grow if playlevel < creaturelevel
    RetDistance -= (float)leveldif;

    if (creaturelevel + 5 <= sWorld.getConfig(CONFIG_UINT32_MAX_PLAYER_LEVEL))
    {
        // detect range auras
        RetDistance += GetTotalAuraModifier(SPELL_AURA_MOD_DETECT_RANGE);

        // detected range auras
        RetDistance += pl->GetTotalAuraModifier(SPELL_AURA_MOD_DETECTED_RANGE);
    }

    // "Minimum Aggro Radius for a mob seems to be combat range (5 yards)"
    if (RetDistance < 5)
        RetDistance = 5;

    return (RetDistance * aggroRate);
}

void Creature::SetDeathState(DeathState s)
{
    if ((s == JUST_DIED && !m_isDeadByDefault) || (s == JUST_ALIVED && m_isDeadByDefault))
    {
        m_corpseDecayTimer = m_corpseDelay * IN_MILLISECONDS; // the max/default time for corpse decay (before creature is looted/AllLootRemovedFromCorpse() is called)
        m_respawnTime = time(nullptr) + m_respawnDelay;        // respawn delay (spawntimesecs)

        // always save boss respawn time at death to prevent crash cheating
        if (sWorld.getConfig(CONFIG_BOOL_SAVE_RESPAWN_TIME_IMMEDIATELY) || IsWorldBoss())
            SaveRespawnTime();
    }

    Unit::SetDeathState(s);

    if (s == JUST_DIED)
    {
        SetTargetGuid(ObjectGuid());                        // remove target selection in any cases (can be set at aura remove in Unit::SetDeathState)
        SetUInt32Value(UNIT_NPC_FLAGS, UNIT_NPC_FLAG_NONE);

        if (HasSearchedAssistance())
        {
            SetNoSearchAssistance(false);
            UpdateSpeed(MOVE_RUN, false);
        }

        if (CanFly())
            i_motionMaster.MoveFall();

        Unit::SetDeathState(CORPSE);
    }

    if (s == JUST_ALIVED)
    {
        clearUnitState(UNIT_STAT_ALL_STATE);

        Unit::SetDeathState(ALIVE);

        SetHealth(GetMaxHealth());
        SetLootRecipient(nullptr);
        if (GetTemporaryFactionFlags() & TEMPFACTION_RESTORE_RESPAWN)
            ClearTemporaryFaction();

        SetMeleeDamageSchool(SpellSchools(GetCreatureInfo()->DamageSchool));

        // Dynamic flags may be adjusted by spells. Clear them
        // first and let spell from *addon apply where needed.
        SetUInt32Value(UNIT_DYNAMIC_FLAGS, UNIT_DYNFLAG_NONE);
        LoadCreatureAddon(true);

        // Flags after LoadCreatureAddon. Any spell in *addon
        // will not be able to adjust these.
        SetUInt32Value(UNIT_NPC_FLAGS, GetCreatureInfo()->NpcFlags);
        RemoveFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_SKINNABLE);

        SetWalk(true, true);
        i_motionMaster.Initialize();
    }
}

void Creature::Respawn()
{
    RemoveCorpse();
    if (!IsInWorld())                                       // Could be removed as part of a pool (in which case respawn-time is handled with pool-system)
        return;

    if (IsDespawned())
    {
        if (HasStaticDBSpawnData())
            GetMap()->GetPersistentState()->SaveCreatureRespawnTime(GetGUIDLow(), 0);
        m_respawnTime = time(nullptr);                         // respawn at next tick
    }
}

void Creature::ForcedDespawn(uint32 timeMSToDespawn)
{
    if (timeMSToDespawn)
    {
        ForcedDespawnDelayEvent* pEvent = new ForcedDespawnDelayEvent(*this);

        m_Events.AddEvent(pEvent, m_Events.CalculateTime(timeMSToDespawn));
        return;
    }

    if (IsDespawned())
        return;

    if (isAlive())
        SetDeathState(JUST_DIED);

    RemoveCorpse();

    SetHealth(0);                                           // just for nice GM-mode view
}

bool Creature::IsImmuneToSpell(SpellEntry const* spellInfo, bool castOnSelf)
{
    if (!spellInfo)
        return false;

    if (!castOnSelf && GetCreatureInfo()->MechanicImmuneMask & (1 << (spellInfo->Mechanic - 1)))
        return true;

    return Unit::IsImmuneToSpell(spellInfo, castOnSelf);
}

bool Creature::IsImmuneToSpellEffect(SpellEntry const* spellInfo, SpellEffectIndex index, bool castOnSelf) const
{
    if (!castOnSelf && GetCreatureInfo()->MechanicImmuneMask & (1 << (spellInfo->EffectMechanic[index] - 1)))
        return true;

    // Taunt immunity special flag check
    if (GetCreatureInfo()->ExtraFlags & CREATURE_FLAG_EXTRA_NOT_TAUNTABLE)
    {
        // Taunt aura apply check
        if (spellInfo->Effect[index] == SPELL_EFFECT_APPLY_AURA)
        {
            if (spellInfo->EffectApplyAuraName[index] == SPELL_AURA_MOD_TAUNT)
                return true;
        }
        // Spell effect taunt check
        else if (spellInfo->Effect[index] == SPELL_EFFECT_ATTACK_ME)
            return true;
    }

    return Unit::IsImmuneToSpellEffect(spellInfo, index, castOnSelf);
}

SpellEntry const* Creature::ReachWithSpellAttack(Unit* pVictim)
{
    if (!pVictim)
        return nullptr;

    for (uint32 i = 0; i < CREATURE_MAX_SPELLS; ++i)
    {
        if (!m_spells[i])
            continue;
        SpellEntry const* spellInfo = sSpellStore.LookupEntry(m_spells[i]);
        if (!spellInfo)
        {
            sLog.outError("WORLD: unknown spell id %i", m_spells[i]);
            continue;
        }

        bool bcontinue = true;
        for (int j = 0; j < MAX_EFFECT_INDEX; ++j)
        {
            if ((spellInfo->Effect[j] == SPELL_EFFECT_SCHOOL_DAMAGE)       ||
                    (spellInfo->Effect[j] == SPELL_EFFECT_INSTAKILL)            ||
                    (spellInfo->Effect[j] == SPELL_EFFECT_ENVIRONMENTAL_DAMAGE) ||
                    (spellInfo->Effect[j] == SPELL_EFFECT_HEALTH_LEECH)
               )
            {
                bcontinue = false;
                break;
            }
        }
        if (bcontinue) continue;

        if (spellInfo->manaCost > GetPower(POWER_MANA))
            continue;
        SpellRangeEntry const* srange = sSpellRangeStore.LookupEntry(spellInfo->rangeIndex);
        float range = GetSpellMaxRange(srange);
        float minrange = GetSpellMinRange(srange);

        float dist = GetCombatDistance(pVictim, spellInfo->rangeIndex == SPELL_RANGE_IDX_COMBAT);

        // if(!isInFront( pVictim, range ) && spellInfo->AttributesEx )
        //    continue;
        if (dist > range || dist < minrange)
            continue;
        if (spellInfo->PreventionType == SPELL_PREVENTION_TYPE_SILENCE && HasFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_SILENCED))
            continue;
        if (spellInfo->PreventionType == SPELL_PREVENTION_TYPE_PACIFY && HasFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_PACIFIED))
            continue;
        return spellInfo;
    }
    return nullptr;
}

SpellEntry const* Creature::ReachWithSpellCure(Unit* pVictim)
{
    if (!pVictim)
        return nullptr;

    for (uint32 i = 0; i < CREATURE_MAX_SPELLS; ++i)
    {
        if (!m_spells[i])
            continue;
        SpellEntry const* spellInfo = sSpellStore.LookupEntry(m_spells[i]);
        if (!spellInfo)
        {
            sLog.outError("WORLD: unknown spell id %i", m_spells[i]);
            continue;
        }

        bool bcontinue = true;
        for (int j = 0; j < MAX_EFFECT_INDEX; ++j)
        {
            if ((spellInfo->Effect[j] == SPELL_EFFECT_HEAL))
            {
                bcontinue = false;
                break;
            }
        }
        if (bcontinue)
            continue;

        if (spellInfo->manaCost > GetPower(POWER_MANA))
            continue;
        SpellRangeEntry const* srange = sSpellRangeStore.LookupEntry(spellInfo->rangeIndex);
        float range = GetSpellMaxRange(srange);
        float minrange = GetSpellMinRange(srange);

        float dist = GetCombatDistance(pVictim, spellInfo->rangeIndex == SPELL_RANGE_IDX_COMBAT);

        // if(!isInFront( pVictim, range ) && spellInfo->AttributesEx )
        //    continue;
        if (dist > range || dist < minrange)
            continue;
        if (spellInfo->PreventionType == SPELL_PREVENTION_TYPE_SILENCE && HasFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_SILENCED))
            continue;
        if (spellInfo->PreventionType == SPELL_PREVENTION_TYPE_PACIFY && HasFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_PACIFIED))
            continue;
        return spellInfo;
    }
    return nullptr;
}

bool Creature::IsVisibleInGridForPlayer(Player* pl) const
{
    // gamemaster in GM mode see all, including ghosts
    if (pl->isGameMaster())
        return true;

    if (GetCreatureInfo()->ExtraFlags & CREATURE_FLAG_EXTRA_INVISIBLE)
        return false;

    // Live player (or with not release body see live creatures or death creatures with corpse disappearing time > 0
    if (pl->isAlive() || pl->GetDeathTimer() > 0)
    {
        return (isAlive() || m_corpseDecayTimer > 0 || (m_isDeadByDefault && m_deathState == CORPSE));
    }

    // Dead player see live creatures near own corpse
    if (isAlive())
    {
        Corpse* corpse = pl->GetCorpse();
        if (corpse)
        {
            // 20 - aggro distance for same level, 25 - max additional distance if player level less that creature level
            if (corpse->IsWithinDistInMap(this, (20 + 25)*sWorld.getConfig(CONFIG_FLOAT_RATE_CREATURE_AGGRO)))
                return true;
        }
    }

    // Dead player can see ghosts
    if (GetCreatureInfo()->CreatureTypeFlags & CREATURE_TYPEFLAGS_GHOST_VISIBLE)
        return true;

    // and not see any other
    return false;
}

void Creature::SendAIReaction(AiReaction reactionType)
{
    WorldPacket data(SMSG_AI_REACTION, 12);

    data << GetObjectGuid();
    data << uint32(reactionType);

    ((WorldObject*)this)->SendMessageToSet(&data, true);

    DEBUG_FILTER_LOG(LOG_FILTER_AI_AND_MOVEGENSS, "WORLD: Sent SMSG_AI_REACTION, type %u.", reactionType);
}

void Creature::CallAssistance()
{
    // FIXME: should player pets call for assistance?
    if (!m_AlreadyCallAssistance && getVictim() && !isCharmed())
    {
        SetNoCallAssistance(true);

        if (GetCreatureInfo()->ExtraFlags & CREATURE_FLAG_EXTRA_NO_CALL_ASSIST)
            return;

        AI()->SendAIEventAround(AI_EVENT_CALL_ASSISTANCE, getVictim(), sWorld.getConfig(CONFIG_UINT32_CREATURE_FAMILY_ASSISTANCE_DELAY), sWorld.getConfig(CONFIG_FLOAT_CREATURE_FAMILY_ASSISTANCE_RADIUS));
    }
}

void Creature::CallForHelp(float fRadius)
{
    if (fRadius <= 0.0f || !getVictim() || IsPet() || isCharmed())
        return;

    MaNGOS::CallOfHelpCreatureInRangeDo u_do(this, getVictim(), fRadius);
    MaNGOS::CreatureWorker<MaNGOS::CallOfHelpCreatureInRangeDo> worker(this, u_do);
    Cell::VisitGridObjects(this, worker, fRadius);
}

/// if enemy provided, check for initial combat help against enemy
bool Creature::CanAssistTo(const Unit* u, const Unit* enemy, bool checkfaction /*= true*/) const
{
    // we don't need help from zombies :)
    if (!isAlive())
        return false;

    // we don't need help from non-combatant ;)
    if (IsCivilian())
        return false;

    if (HasFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_NON_ATTACKABLE | UNIT_FLAG_NOT_SELECTABLE | UNIT_FLAG_PASSIVE))
        return false;

    // skip fighting creature
    if (enemy && isInCombat())
        return false;

    // only free creature
    if (GetCharmerOrOwnerGuid())
        return false;

    // only from same creature faction
    if (checkfaction)
    {
        if (getFaction() != u->getFaction())
            return false;
    }
    else
    {
        if (!IsFriendlyTo(u))
            return false;
    }

    // skip non hostile to caster enemy creatures
    if (enemy && !IsHostileTo(enemy))
        return false;

    return true;
}

bool Creature::CanInitiateAttack()
{
    if (hasUnitState(UNIT_STAT_STUNNED | UNIT_STAT_DIED))
        return false;

    if (HasFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_NON_ATTACKABLE | UNIT_FLAG_NOT_SELECTABLE))
        return false;

    if (isPassiveToHostile())
        return false;

    if (m_aggroDelay != 0)
        return false;

    if (!CanAttackByItself())
        return false;

    return true;
}

void Creature::SaveRespawnTime()
{
    if (IsPet() || !HasStaticDBSpawnData())
        return;

    if (m_respawnTime > time(nullptr))                         // dead (no corpse)
        GetMap()->GetPersistentState()->SaveCreatureRespawnTime(GetGUIDLow(), m_respawnTime);
    else if (m_corpseDecayTimer > 0)                        // dead (corpse)
        GetMap()->GetPersistentState()->SaveCreatureRespawnTime(GetGUIDLow(), time(nullptr) + m_respawnDelay + m_corpseDecayTimer / IN_MILLISECONDS);
}

bool Creature::IsOutOfThreatArea(Unit* pVictim) const
{
    if (!pVictim)
        return true;

    if (!pVictim->IsInMap(this))
        return true;

    if (!pVictim->isTargetableForAttack())
        return true;

    if (!pVictim->isInAccessablePlaceFor(this))
        return true;

    if (!pVictim->isVisibleForOrDetect(this, this, false))
        return true;

    if (sMapStore.LookupEntry(GetMapId())->IsDungeon())
        return false;

    float AttackDist = GetAttackDistance(pVictim);
    float ThreatRadius = sWorld.getConfig(CONFIG_FLOAT_THREAT_RADIUS);

    // Use AttackDistance in distance check if threat radius is lower. This prevents creature bounce in and out of combat every update tick.
    return !pVictim->IsWithinDist3d(m_combatStartX, m_combatStartY, m_combatStartZ,
                                    ThreatRadius > AttackDist ? ThreatRadius : AttackDist);
}

CreatureDataAddon const* Creature::GetCreatureAddon() const
{
    if (CreatureDataAddon const* addon = ObjectMgr::GetCreatureAddon(GetGUIDLow()))
        return addon;

    // dependent from difficulty mode entry
    if (GetEntry() != GetCreatureInfo()->Entry)
    {
        // If CreatureTemplateAddon for difficulty_entry_N exist, it's there for a reason
        if (CreatureDataAddon const* addon =  ObjectMgr::GetCreatureTemplateAddon(GetCreatureInfo()->Entry))
            return addon;
    }

    // Return CreatureTemplateAddon when nothing else exist
    return ObjectMgr::GetCreatureTemplateAddon(GetEntry());
}

// creature_addon table
bool Creature::LoadCreatureAddon(bool reload)
{
    CreatureDataAddon const* cainfo = GetCreatureAddon();
    if (!cainfo)
        return false;

    if (cainfo->mount != 0)
        Mount(cainfo->mount);

    if (cainfo->bytes1 != 0)
    {
        // 0 StandState
        // 1 FreeTalentPoints   Pet only, so always 0 for default creature
        // 2 StandFlags
        // 3 StandMiscFlags

        SetByteValue(UNIT_FIELD_BYTES_1, 0, uint8(cainfo->bytes1 & 0xFF));
        // SetByteValue(UNIT_FIELD_BYTES_1, 1, uint8((cainfo->bytes1 >> 8) & 0xFF));
        SetByteValue(UNIT_FIELD_BYTES_1, 1, 0);
        SetByteValue(UNIT_FIELD_BYTES_1, 2, uint8((cainfo->bytes1 >> 16) & 0xFF));
        SetByteValue(UNIT_FIELD_BYTES_1, 3, uint8((cainfo->bytes1 >> 24) & 0xFF));
    }

    // UNIT_FIELD_BYTES_2
    // 0 SheathState
    // 1 UnitPVPStateFlags  Set at Creature::UpdateEntry (SetPvp())
    // 2 UnitRename         Pet only, so always 0 for default creature
    // 3 ShapeshiftForm     Must be determined/set by shapeshift spell/aura
    SetByteValue(UNIT_FIELD_BYTES_2, 0, cainfo->sheath_state);

    if (cainfo->pvp_state != 0)
        SetByteValue(UNIT_FIELD_BYTES_2, 1, cainfo->pvp_state);

    // SetByteValue(UNIT_FIELD_BYTES_2, 2, 0);
    // SetByteValue(UNIT_FIELD_BYTES_2, 3, 0);

    if (cainfo->emote != 0)
        SetUInt32Value(UNIT_NPC_EMOTESTATE, cainfo->emote);

    if (cainfo->splineFlags & SPLINEFLAG_FLYING)
        SetLevitate(true);

    if (cainfo->auras)
    {
        for (uint32 const* cAura = cainfo->auras; *cAura; ++cAura)
        {
            if (HasAuraOfDifficulty(*cAura))
            {
                if (!reload)
                    sLog.outErrorDb("Creature (GUIDLow: %u Entry: %u) has spell %u in `auras` field, but aura is already applied.", GetGUIDLow(), GetEntry(), *cAura);

                continue;
            }

            SpellEntry const* spellInfo = sSpellStore.LookupEntry(*cAura);  // Already checked on load

            // Get Difficulty mode for initial case (npc not yet added to world)
            if (spellInfo->SpellDifficultyId && !reload && GetMap()->IsDungeon())
                if (SpellEntry const* spellEntry = GetSpellEntryByDifficulty(spellInfo->SpellDifficultyId, GetMap()->GetDifficulty(), GetMap()->IsRaid()))
                    spellInfo = spellEntry;

            CastSpell(this, spellInfo, true);
        }
    }
    return true;
}

/// Sends a message to LocalDefense and WorldDefense channels for players of the other team
void Creature::SendZoneUnderAttackMessage(Player* attacker)
{
    sWorld.SendZoneUnderAttackMessage(GetZoneId(), attacker->GetTeam() == ALLIANCE ? HORDE : ALLIANCE);
}

void Creature::SetInCombatWithZone()
{
    if (!CanHaveThreatList())
    {
        sLog.outError("Creature entry %u call SetInCombatWithZone but creature cannot have threat list.", GetEntry());
        return;
    }

    Map* pMap = GetMap();

    if (!pMap->IsDungeon())
    {
        sLog.outError("Creature entry %u call SetInCombatWithZone for map (id: %u) that isn't an instance.", GetEntry(), pMap->GetId());
        return;
    }

    Map::PlayerList const& PlList = pMap->GetPlayers();

    if (PlList.isEmpty())
        return;

    for (Map::PlayerList::const_iterator i = PlList.begin(); i != PlList.end(); ++i)
    {
        if (Player* pPlayer = i->getSource())
        {
            if (pPlayer->isGameMaster())
                continue;

            if (pPlayer->isAlive() && !IsFriendlyTo(pPlayer))
            {
                pPlayer->SetInCombatWith(this);
                AddThreat(pPlayer);
            }
        }
    }
}

bool Creature::MeetsSelectAttackingRequirement(Unit* pTarget, SpellEntry const* pSpellInfo, uint32 selectFlags) const
{
    if (selectFlags & SELECT_FLAG_PLAYER && pTarget->GetTypeId() != TYPEID_PLAYER)
        return false;

    if (selectFlags & SELECT_FLAG_POWER_MANA && pTarget->GetPowerType() != POWER_MANA)
        return false;
    else if (selectFlags & SELECT_FLAG_POWER_RAGE && pTarget->GetPowerType() != POWER_RAGE)
        return false;
    else if (selectFlags & SELECT_FLAG_POWER_ENERGY && pTarget->GetPowerType() != POWER_ENERGY)
        return false;
    else if (selectFlags & SELECT_FLAG_POWER_RUNIC && pTarget->GetPowerType() != POWER_RUNIC_POWER)
        return false;

    if (selectFlags & SELECT_FLAG_IN_MELEE_RANGE && !CanReachWithMeleeAttack(pTarget))
        return false;
    if (selectFlags & SELECT_FLAG_NOT_IN_MELEE_RANGE && CanReachWithMeleeAttack(pTarget))
        return false;

    if (selectFlags & SELECT_FLAG_IN_LOS && !IsWithinLOSInMap(pTarget))
        return false;

    if (pSpellInfo)
    {
        switch (pSpellInfo->rangeIndex)
        {
            case SPELL_RANGE_IDX_SELF_ONLY: return false;
            case SPELL_RANGE_IDX_ANYWHERE:  return true;
            case SPELL_RANGE_IDX_COMBAT:    return CanReachWithMeleeAttack(pTarget);
        }

        SpellRangeEntry const* srange = sSpellRangeStore.LookupEntry(pSpellInfo->rangeIndex);
        float max_range = GetSpellMaxRange(srange);
        float min_range = GetSpellMinRange(srange);
        float dist = GetCombatDistance(pTarget, false);

        return dist < max_range && dist >= min_range;
    }

    return true;
}

Unit* Creature::SelectAttackingTarget(AttackingTarget target, uint32 position, uint32 uiSpellEntry, uint32 selectFlags) const
{
    return SelectAttackingTarget(target, position, sSpellStore.LookupEntry(uiSpellEntry), selectFlags);
}

Unit* Creature::SelectAttackingTarget(AttackingTarget target, uint32 position, SpellEntry const* pSpellInfo /*= nullptr*/, uint32 selectFlags/*= 0*/) const
{
    if (!CanHaveThreatList())
        return nullptr;

    // ThreatList m_threatlist;
    ThreatList const& threatlist = getThreatManager().getThreatList();
    ThreatList::const_iterator itr = threatlist.begin();
    ThreatList::const_reverse_iterator ritr = threatlist.rbegin();

    if (position >= threatlist.size() || !threatlist.size())
        return nullptr;

    switch (target)
    {
        case ATTACKING_TARGET_RANDOM:
        {
            std::vector<Unit*> suitableUnits;
            suitableUnits.reserve(threatlist.size() - position);
            advance(itr, position);
            for (; itr != threatlist.end(); ++itr)
                if (Unit* pTarget = GetMap()->GetUnit((*itr)->getUnitGuid()))
                    if (!selectFlags || MeetsSelectAttackingRequirement(pTarget, pSpellInfo, selectFlags))
                        suitableUnits.push_back(pTarget);

            if (!suitableUnits.empty())
                return suitableUnits[urand(0, suitableUnits.size() - 1)];

            break;
        }
        case ATTACKING_TARGET_TOPAGGRO:
        {
            advance(itr, position);
            for (; itr != threatlist.end(); ++itr)
                if (Unit* pTarget = GetMap()->GetUnit((*itr)->getUnitGuid()))
                    if (!selectFlags || MeetsSelectAttackingRequirement(pTarget, pSpellInfo, selectFlags))
                        return pTarget;

            break;
        }
        case ATTACKING_TARGET_BOTTOMAGGRO:
        {
            advance(ritr, position);
            for (; ritr != threatlist.rend(); ++ritr)
                if (Unit* pTarget = GetMap()->GetUnit((*itr)->getUnitGuid()))
                    if (!selectFlags || MeetsSelectAttackingRequirement(pTarget, pSpellInfo, selectFlags))
                        return pTarget;

            break;
        }
    }

    return nullptr;
}

void Creature::_AddCreatureSpellCooldown(uint32 spell_id, time_t end_time)
{
    m_CreatureSpellCooldowns[spell_id] = end_time;
}

void Creature::_AddCreatureCategoryCooldown(uint32 category, time_t apply_time)
{
    m_CreatureCategoryCooldowns[category] = apply_time;
}

void Creature::AddCreatureSpellCooldown(uint32 spellid)
{
    SpellEntry const* spellInfo = sSpellStore.LookupEntry(spellid);
    if (!spellInfo)
        return;

    uint32 cooldown = GetSpellRecoveryTime(spellInfo);
    if (cooldown)
        _AddCreatureSpellCooldown(spellid, time(nullptr) + cooldown / IN_MILLISECONDS);

    if (spellInfo->Category)
        _AddCreatureCategoryCooldown(spellInfo->Category, time(nullptr));
}

bool Creature::HasCategoryCooldown(uint32 spell_id) const
{
    SpellEntry const* spellInfo = sSpellStore.LookupEntry(spell_id);
    if (!spellInfo)
        return false;

    CreatureSpellCooldowns::const_iterator itr = m_CreatureCategoryCooldowns.find(spellInfo->Category);
    return (itr != m_CreatureCategoryCooldowns.end() && time_t(itr->second + (spellInfo->CategoryRecoveryTime / IN_MILLISECONDS)) > time(nullptr));
}

bool Creature::HasSpellCooldown(uint32 spell_id) const
{
    CreatureSpellCooldowns::const_iterator itr = m_CreatureSpellCooldowns.find(spell_id);
    return (itr != m_CreatureSpellCooldowns.end() && itr->second > time(nullptr)) || HasCategoryCooldown(spell_id);
}

uint8 Creature::getRace() const
{
    uint8 race = Unit::getRace();
    return race ? race : GetCreatureModelRace(GetNativeDisplayId());
}

bool Creature::IsInEvadeMode() const
{
    return !i_motionMaster.empty() && i_motionMaster.GetCurrentMovementGeneratorType() == HOME_MOTION_TYPE;
}

bool Creature::HasSpell(uint32 spellID) const
{
    uint8 i;
    for (i = 0; i < CREATURE_MAX_SPELLS; ++i)
        if (spellID == m_spells[i])
            break;
    return i < CREATURE_MAX_SPELLS;                         // break before end of iteration of known spells
}

time_t Creature::GetRespawnTimeEx() const
{
    time_t now = time(nullptr);
    if (m_respawnTime > now)                                // dead (no corpse)
        return m_respawnTime;
    else if (m_corpseDecayTimer > 0)                        // dead (corpse)
        return now + m_respawnDelay + m_corpseDecayTimer / IN_MILLISECONDS;
    else
        return now;
}

void Creature::GetRespawnCoord(float& x, float& y, float& z, float* ori, float* dist) const
{
    x = m_respawnPos.x;
    y = m_respawnPos.y;
    z = m_respawnPos.z;

    if (ori)
        *ori = m_respawnPos.o;

    if (dist)
        *dist = GetRespawnRadius();

    // lets check if our creatures have valid spawn coordinates
    MANGOS_ASSERT(MaNGOS::IsValidMapCoord(x, y, z) || PrintCoordinatesError(x, y, z, "respawn"));
}

void Creature::ResetRespawnCoord()
{
    if (CreatureData const* data = sObjectMgr.GetCreatureData(GetGUIDLow()))
    {
        m_respawnPos.x = data->posX;
        m_respawnPos.y = data->posY;
        m_respawnPos.z = data->posZ;
        m_respawnPos.o = data->orientation;
    }
}

uint32 Creature::GetLevelForTarget(Unit const* target) const
{
    if (!IsWorldBoss())
        return Unit::GetLevelForTarget(target);

    uint32 level = target->getLevel() + sWorld.getConfig(CONFIG_UINT32_WORLD_BOSS_LEVEL_DIFF);
    if (level < 1)
        return 1;
    if (level > 255)
        return 255;
    return level;
}

std::string Creature::GetAIName() const
{
    return ObjectMgr::GetCreatureTemplate(GetEntry())->AIName;
}

std::string Creature::GetScriptName() const
{
    return sScriptMgr.GetScriptName(GetScriptId());
}

uint32 Creature::GetScriptId() const
{
    return ObjectMgr::GetCreatureTemplate(GetEntry())->ScriptID;
}

VendorItemData const* Creature::GetVendorItems() const
{
    return sObjectMgr.GetNpcVendorItemList(GetEntry());
}

VendorItemData const* Creature::GetVendorTemplateItems() const
{
    uint32 vendorId = GetCreatureInfo()->VendorTemplateId;
    return vendorId ? sObjectMgr.GetNpcVendorTemplateItemList(vendorId) : nullptr;
}

uint32 Creature::GetVendorItemCurrentCount(VendorItem const* vItem)
{
    if (!vItem->maxcount)
        return vItem->maxcount;

    VendorItemCounts::iterator itr = m_vendorItemCounts.begin();
    for (; itr != m_vendorItemCounts.end(); ++itr)
        if (itr->itemId == vItem->item)
            break;

    if (itr == m_vendorItemCounts.end())
        return vItem->maxcount;

    VendorItemCount* vCount = &*itr;

    time_t ptime = time(nullptr);

    if (vCount->lastIncrementTime + vItem->incrtime <= ptime)
    {
        ItemPrototype const* pProto = ObjectMgr::GetItemPrototype(vItem->item);

        uint32 diff = uint32((ptime - vCount->lastIncrementTime) / vItem->incrtime);
        if ((vCount->count + diff * pProto->BuyCount) >= vItem->maxcount)
        {
            m_vendorItemCounts.erase(itr);
            return vItem->maxcount;
        }

        vCount->count += diff * pProto->BuyCount;
        vCount->lastIncrementTime = ptime;
    }

    return vCount->count;
}

uint32 Creature::UpdateVendorItemCurrentCount(VendorItem const* vItem, uint32 used_count)
{
    if (!vItem->maxcount)
        return 0;

    VendorItemCounts::iterator itr = m_vendorItemCounts.begin();
    for (; itr != m_vendorItemCounts.end(); ++itr)
        if (itr->itemId == vItem->item)
            break;

    if (itr == m_vendorItemCounts.end())
    {
        uint32 new_count = vItem->maxcount > used_count ? vItem->maxcount - used_count : 0;
        m_vendorItemCounts.push_back(VendorItemCount(vItem->item, new_count));
        return new_count;
    }

    VendorItemCount* vCount = &*itr;

    time_t ptime = time(nullptr);

    if (vCount->lastIncrementTime + vItem->incrtime <= ptime)
    {
        ItemPrototype const* pProto = ObjectMgr::GetItemPrototype(vItem->item);

        uint32 diff = uint32((ptime - vCount->lastIncrementTime) / vItem->incrtime);
        if ((vCount->count + diff * pProto->BuyCount) < vItem->maxcount)
            vCount->count += diff * pProto->BuyCount;
        else
            vCount->count = vItem->maxcount;
    }

    vCount->count = vCount->count > used_count ? vCount->count - used_count : 0;
    vCount->lastIncrementTime = ptime;
    return vCount->count;
}

TrainerSpellData const* Creature::GetTrainerTemplateSpells() const
{
    uint32 trainerId = GetCreatureInfo()->TrainerTemplateId;
    return trainerId ? sObjectMgr.GetNpcTrainerTemplateSpells(trainerId) : nullptr;
}

TrainerSpellData const* Creature::GetTrainerSpells() const
{
    return sObjectMgr.GetNpcTrainerSpells(GetEntry());
}

// overwrite WorldObject function for proper name localization
const char* Creature::GetNameForLocaleIdx(int32 loc_idx) const
{
    char const* name = GetName();
    sObjectMgr.GetCreatureLocaleStrings(GetEntry(), loc_idx, &name);
    return name;
}

void Creature::SetFactionTemporary(uint32 factionId, uint32 tempFactionFlags)
{
    m_temporaryFactionFlags = tempFactionFlags;
    setFaction(factionId);

    if (m_temporaryFactionFlags & TEMPFACTION_TOGGLE_NON_ATTACKABLE)
        RemoveFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_NON_ATTACKABLE);
    if (m_temporaryFactionFlags & TEMPFACTION_TOGGLE_OOC_NOT_ATTACK)
        RemoveFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_OOC_NOT_ATTACKABLE);
    if (m_temporaryFactionFlags & TEMPFACTION_TOGGLE_PASSIVE)
        RemoveFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_PASSIVE);
    if (m_temporaryFactionFlags & TEMPFACTION_TOGGLE_PACIFIED)
        RemoveFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_PACIFIED);
    if (m_temporaryFactionFlags & TEMPFACTION_TOGGLE_NOT_SELECTABLE)
        RemoveFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_NOT_SELECTABLE);
}

void Creature::ClearTemporaryFaction()
{
    // No restore if creature is charmed/possessed.
    // For later we may consider extend to restore to charmer faction where charmer is creature.
    // This can also be done by update any pet/charmed of creature at any faction change to charmer.
    if (isCharmed())
        return;

    // Reset to original faction
    setFaction(GetCreatureInfo()->FactionAlliance);
    // Reset UNIT_FLAG_NON_ATTACKABLE, UNIT_FLAG_OOC_NOT_ATTACKABLE, UNIT_FLAG_PASSIVE, UNIT_FLAG_PACIFIED or UNIT_FLAG_NOT_SELECTABLE flags
    if (m_temporaryFactionFlags & TEMPFACTION_TOGGLE_NON_ATTACKABLE && GetCreatureInfo()->UnitFlags & UNIT_FLAG_NON_ATTACKABLE)
        SetFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_NON_ATTACKABLE);
    if (m_temporaryFactionFlags & TEMPFACTION_TOGGLE_OOC_NOT_ATTACK && GetCreatureInfo()->UnitFlags & UNIT_FLAG_OOC_NOT_ATTACKABLE && !isInCombat())
        SetFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_OOC_NOT_ATTACKABLE);
    if (m_temporaryFactionFlags & TEMPFACTION_TOGGLE_PASSIVE && GetCreatureInfo()->UnitFlags & UNIT_FLAG_PASSIVE)
        SetFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_PASSIVE);
    if (m_temporaryFactionFlags & TEMPFACTION_TOGGLE_PACIFIED && GetCreatureInfo()->UnitFlags & UNIT_FLAG_PACIFIED)
        SetFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_PACIFIED);
    if (m_temporaryFactionFlags & TEMPFACTION_TOGGLE_NOT_SELECTABLE && GetCreatureInfo()->UnitFlags & UNIT_FLAG_NOT_SELECTABLE)
        SetFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_NOT_SELECTABLE);

    m_temporaryFactionFlags = TEMPFACTION_NONE;
}

void Creature::SendAreaSpiritHealerQueryOpcode(Player* pl)
{
    uint32 next_resurrect = 0;
    if (Spell* pcurSpell = GetCurrentSpell(CURRENT_CHANNELED_SPELL))
        next_resurrect = pcurSpell->GetCastedTime();
    WorldPacket data(SMSG_AREA_SPIRIT_HEALER_TIME, 8 + 4);
    data << ObjectGuid(GetObjectGuid());
    data << uint32(next_resurrect);
    pl->SendDirectMessage(&data);
}

void Creature::ApplyGameEventSpells(GameEventCreatureData const* eventData, bool activated)
{
    uint32 cast_spell = activated ? eventData->spell_id_start : eventData->spell_id_end;
    uint32 remove_spell = activated ? eventData->spell_id_end : eventData->spell_id_start;

    if (remove_spell)
        if (SpellEntry const* spellEntry = sSpellStore.LookupEntry(remove_spell))
            if (IsSpellAppliesAura(spellEntry))
                RemoveAurasDueToSpell(remove_spell);

    if (cast_spell)
        CastSpell(this, cast_spell, true);
}

void Creature::FillGuidsListFromThreatList(GuidVector& guids, uint32 maxamount /*= 0*/)
{
    if (!CanHaveThreatList())
        return;

    ThreatList const& threats = getThreatManager().getThreatList();

    maxamount = maxamount > 0 ? std::min(maxamount, uint32(threats.size())) : threats.size();

    guids.reserve(guids.size() + maxamount);

    for (ThreatList::const_iterator itr = threats.begin(); maxamount && itr != threats.end(); ++itr, --maxamount)
        guids.push_back((*itr)->getUnitGuid());
}

struct AddCreatureToRemoveListInMapsWorker
{
    AddCreatureToRemoveListInMapsWorker(ObjectGuid guid) : i_guid(guid) {}

    void operator()(Map* map)
    {
        if (Creature* pCreature = map->GetCreature(i_guid))
            pCreature->AddObjectToRemoveList();
    }

    ObjectGuid i_guid;
};

void Creature::AddToRemoveListInMaps(uint32 db_guid, CreatureData const* data)
{
    AddCreatureToRemoveListInMapsWorker worker(data->GetObjectGuid(db_guid));
    sMapMgr.DoForAllMapsWithMapId(data->mapid, worker);
}

struct SpawnCreatureInMapsWorker
{
    SpawnCreatureInMapsWorker(uint32 guid, CreatureData const* data)
        : i_guid(guid), i_data(data) {}

    void operator()(Map* map)
    {
        // We use spawn coords to spawn
        if (map->IsLoaded(i_data->posX, i_data->posY))
        {
            Creature* pCreature = new Creature;
            // DEBUG_LOG("Spawning creature %u",*itr);
            if (!pCreature->LoadFromDB(i_guid, map))
            {
                delete pCreature;
            }
            else
            {
                map->Add(pCreature);
            }
        }
    }

    uint32 i_guid;
    CreatureData const* i_data;
};

void Creature::SpawnInMaps(uint32 db_guid, CreatureData const* data)
{
    SpawnCreatureInMapsWorker worker(db_guid, data);
    sMapMgr.DoForAllMapsWithMapId(data->mapid, worker);
}

bool Creature::HasStaticDBSpawnData() const
{
    return sObjectMgr.GetCreatureData(GetGUIDLow()) != nullptr;
}

void Creature::SetWalk(bool enable, bool asDefault)
{
    if (asDefault)
    {
        if (enable)
            clearUnitState(UNIT_STAT_RUNNING);
        else
            addUnitState(UNIT_STAT_RUNNING);
    }

    // Nothing changed?
    if (enable == m_movementInfo.HasMovementFlag(MOVEFLAG_WALK_MODE))
        return;

    if (enable)
        m_movementInfo.AddMovementFlag(MOVEFLAG_WALK_MODE);
    else
        m_movementInfo.RemoveMovementFlag(MOVEFLAG_WALK_MODE);

    WorldPacket data(enable ? SMSG_SPLINE_MOVE_SET_WALK_MODE : SMSG_SPLINE_MOVE_SET_RUN_MODE, 9);
    data << GetPackGUID();
    SendMessageToSet(&data, true);
}

void Creature::SetLevitate(bool enable)
{
    if (enable)
        m_movementInfo.AddMovementFlag(MOVEFLAG_LEVITATING);
    else
        m_movementInfo.RemoveMovementFlag(MOVEFLAG_LEVITATING);

    WorldPacket data(enable ? SMSG_SPLINE_MOVE_GRAVITY_DISABLE : SMSG_SPLINE_MOVE_GRAVITY_ENABLE, 9);
    data << GetPackGUID();
    SendMessageToSet(&data, true);
}

void Creature::SetSwim(bool enable)
{
    if (enable)
        m_movementInfo.AddMovementFlag(MOVEFLAG_SWIMMING);
    else
        m_movementInfo.RemoveMovementFlag(MOVEFLAG_SWIMMING);

    WorldPacket data(enable ? SMSG_SPLINE_MOVE_START_SWIM : SMSG_SPLINE_MOVE_STOP_SWIM);
    data << GetPackGUID();
    SendMessageToSet(&data, true);
}

void Creature::SetCanFly(bool enable)
{
    if (enable)
        m_movementInfo.AddMovementFlag(MOVEFLAG_CAN_FLY);
    else
        m_movementInfo.RemoveMovementFlag(MOVEFLAG_CAN_FLY);

    WorldPacket data(enable ? SMSG_SPLINE_MOVE_SET_FLYING : SMSG_SPLINE_MOVE_UNSET_FLYING, 9);
    data << GetPackGUID();
    SendMessageToSet(&data, true);
}

void Creature::SetFeatherFall(bool enable)
{
    if (enable)
        m_movementInfo.AddMovementFlag(MOVEFLAG_SAFE_FALL);
    else
        m_movementInfo.RemoveMovementFlag(MOVEFLAG_SAFE_FALL);

    WorldPacket data(enable ? SMSG_SPLINE_MOVE_FEATHER_FALL : SMSG_SPLINE_MOVE_NORMAL_FALL);
    data << GetPackGUID();
    SendMessageToSet(&data, true);
}

void Creature::SetHover(bool enable)
{
    if (enable)
        m_movementInfo.AddMovementFlag(MOVEFLAG_HOVER);
    else
        m_movementInfo.RemoveMovementFlag(MOVEFLAG_HOVER);

    WorldPacket data(enable ? SMSG_SPLINE_MOVE_SET_HOVER : SMSG_SPLINE_MOVE_UNSET_HOVER, 9);
    data << GetPackGUID();
    SendMessageToSet(&data, false);
}

void Creature::SetRoot(bool enable)
{
    if (enable)
        m_movementInfo.AddMovementFlag(MOVEFLAG_ROOT);
    else
        m_movementInfo.RemoveMovementFlag(MOVEFLAG_ROOT);

    WorldPacket data(enable ? SMSG_SPLINE_MOVE_ROOT : SMSG_SPLINE_MOVE_UNROOT, 9);
    data << GetPackGUID();
    SendMessageToSet(&data, true);
}

void Creature::SetWaterWalk(bool enable)
{
    if (enable)
        m_movementInfo.AddMovementFlag(MOVEFLAG_WATERWALKING);
    else
        m_movementInfo.RemoveMovementFlag(MOVEFLAG_WATERWALKING);

    WorldPacket data(enable ? SMSG_SPLINE_MOVE_WATER_WALK : SMSG_SPLINE_MOVE_LAND_WALK, 9);
    data << GetPackGUID();
    SendMessageToSet(&data, true);
}

// Set loot status. Also handle remove corpse timer
void Creature::SetLootStatus(CreatureLootStatus status)
{
    if (status <= m_lootStatus)
        return;

    m_lootStatus = status;
    switch (status)
    {
        case CREATURE_LOOT_STATUS_LOOTED:
            if (m_creatureInfo->SkinningLootId)
                SetFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_SKINNABLE);
            else
                RemoveFlag(UNIT_DYNAMIC_FLAGS, UNIT_DYNFLAG_LOOTABLE);
            break;
        case CREATURE_LOOT_STATUS_SKINNED:
            m_corpseDecayTimer = 0; // remove corpse at next update
            RemoveFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_SKINNABLE);
            RemoveFlag(UNIT_DYNAMIC_FLAGS, UNIT_DYNFLAG_LOOTABLE);
            break;
        case CREATURE_LOOT_STATUS_SKIN_AVAILABLE:
            SetFlag(UNIT_FIELD_FLAGS, UNIT_DYNFLAG_LOOTABLE);
            RemoveFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_SKINNABLE);
            break;
        default:
            break;
    }
}

// simple tap system return true if player or his group tapped the creature
// TODO:: this is semi correct. For group situation need more work but its not a big issue
bool Creature::IsTappedBy(Player* plr) const
{
    if (Player* recipient = GetLootRecipient())
    {
        if (recipient == plr)
            return true;

        if (Group* grp = recipient->GetGroup())
        {
            if (Group* plrGroup = plr->GetGroup())
            {
                if (plrGroup == grp)
                    return true;
            }
        }
        return false;
    }
    return false;
}

void Creature::SetStatsBasedOnPlayerMaxLevel()
{
    uint32 maxPlayerLevel = sMapMgr.GetMaxPlayerLevel();
    GameDifficulty gameDifficulty = sMapMgr.GetCurrentDifficulty();
    uint32 currentLevel = this->getLevel();

    bool needToRefreshStats = currentLevel != maxPlayerLevel || m_currentLevel != maxPlayerLevel || m_currentDifficulty != gameDifficulty;
    if (needToRefreshStats)
    {
        this->SetLevel(maxPlayerLevel);
        m_currentLevel = maxPlayerLevel;
        m_currentDifficulty = gameDifficulty;

        for (int i = 0; i < UNIT_MOD_END; ++i)
        {
            m_auraModifiersGroup[i][BASE_VALUE] = 0.0f;
            m_auraModifiersGroup[i][BASE_PCT] = 1.0f;
            m_auraModifiersGroup[i][TOTAL_VALUE] = 0.0f;
            m_auraModifiersGroup[i][TOTAL_PCT] = 1.0f;
        }

        // implement 50% base damage from offhand
        m_auraModifiersGroup[UNIT_MOD_DAMAGE_OFFHAND][TOTAL_PCT] = 0.5f;

        for (int i = 0; i < MAX_ATTACK; ++i)
        {
            m_weaponDamage[i][MINDAMAGE] = BASE_MINDAMAGE;
            m_weaponDamage[i][MAXDAMAGE] = BASE_MAXDAMAGE;
        }

        for (int i = 0; i < MAX_STATS; ++i)
            m_createStats[i] = 0.0f;

        m_attacking = nullptr;
        m_modMeleeHitChance = 0.0f;
        m_modRangedHitChance = 0.0f;
        m_modSpellHitChance = 0.0f;
        m_baseSpellCritChance = 5;

        //SetModifierValue(UNIT_MOD_ATTACK_POWER, BASE_VALUE, 0.0f);
        //SetModifierValue(UNIT_MOD_ATTACK_POWER_RANGED, BASE_VALUE, 0.0f);
        SetInt32Value(UNIT_FIELD_ATTACK_POWER, 0);
        SetInt32Value(UNIT_FIELD_ATTACK_POWER_MODS, 0);
        SetFloatValue(UNIT_FIELD_ATTACK_POWER_MULTIPLIER, 0.0f);
        SetInt32Value(UNIT_FIELD_RANGED_ATTACK_POWER, 0);
        SetInt32Value(UNIT_FIELD_RANGED_ATTACK_POWER_MODS, 0);
        SetFloatValue(UNIT_FIELD_RANGED_ATTACK_POWER_MULTIPLIER, 0.0f);

        InitStatsForLevel();
        UpdateAllStats();
    }
}

bool Creature::UpdateStats(Stats stat)
{
    if (stat > STAT_SPIRIT)
        return false;

    // value = ((base_value * base_pct) + total_value) * total_pct
    float value = GetTotalStatValue(stat);

    SetStat(stat, int32(value));

    if (stat == STAT_STAMINA || stat == STAT_INTELLECT)
    {
        Pet* pet = GetPet();
        if (pet)
            pet->UpdateStats(stat);
    }

    switch (stat)
    {
        case STAT_STRENGTH:
            //UpdateShieldBlockValue();
            break;
        case STAT_AGILITY:
            UpdateArmor();
            //UpdateAllCritPercentages();
            //UpdateDodgePercentage();
            break;
        case STAT_STAMINA:   UpdateMaxHealth(); break;
        case STAT_INTELLECT:
            UpdateMaxPower(POWER_MANA);
            //UpdateAllSpellCritChances();
            UpdateArmor();                                  // SPELL_AURA_MOD_RESISTANCE_OF_INTELLECT_PERCENT, only armor currently
            break;

        case STAT_SPIRIT:
            break;

        default:
            break;
    }
    // Need update (exist AP from stat auras)
    UpdateAttackPowerAndDamage();
    UpdateAttackPowerAndDamage(true);

    //UpdateSpellDamageAndHealingBonus();
    UpdateManaRegen();

    //// Update ratings in exist SPELL_AURA_MOD_RATING_FROM_STAT and only depends from stat
    //uint32 mask = 0;
    //AuraList const& modRatingFromStat = GetAurasByType(SPELL_AURA_MOD_RATING_FROM_STAT);
    //for (AuraList::const_iterator i = modRatingFromStat.begin(); i != modRatingFromStat.end(); ++i)
    //    if (Stats((*i)->GetMiscBValue()) == stat)
    //        mask |= (*i)->GetMiscValue();
    //if (mask)
    //{
    //    for (uint32 rating = 0; rating < MAX_COMBAT_RATING; ++rating)
    //        if (mask & (1 << rating))
    //            ApplyRatingMod(CombatRating(rating), 0, true);
    //}
    return true;
}

bool Creature::UpdateAllStats()
{
    for (int i = STAT_STRENGTH; i < MAX_STATS; ++i)
    {
        float value = GetTotalStatValue(Stats(i));
        SetStat(Stats(i), (int32)value);
    }

    UpdateArmor();
    // calls UpdateAttackPowerAndDamage() in UpdateArmor for SPELL_AURA_MOD_ATTACK_POWER_OF_ARMOR
    UpdateAttackPowerAndDamage(true);
    UpdateMaxHealth();

    for (int i = POWER_MANA; i < MAX_POWERS; ++i)
        UpdateMaxPower(Powers(i));

    //UpdateAllRatings();
    //UpdateAllCritPercentages();
    //UpdateAllSpellCritChances();
    //UpdateDefenseBonusesMod();
    //UpdateShieldBlockValue();
    //UpdateArmorPenetration();
    //UpdateSpellDamageAndHealingBonus();
    UpdateManaRegen();
    //UpdateExpertise(BASE_ATTACK);
    //UpdateExpertise(OFF_ATTACK);
    for (int i = SPELL_SCHOOL_NORMAL; i < MAX_SPELL_SCHOOL; ++i)
        UpdateResistances(i);

    return true;
}

void Creature::UpdateResistances(uint32 school)
{
    if (school > SPELL_SCHOOL_NORMAL)
    {
        float value = GetTotalAuraModValue(UnitMods(UNIT_MOD_RESISTANCE_START + school));
        SetResistance(SpellSchools(school), int32(value));

        Pet* pet = GetPet();
        if (pet)
            pet->UpdateResistances(school);
    }
    else
        UpdateArmor();
}

void Creature::UpdateArmor()
{
    float value;
    UnitMods unitMod = UNIT_MOD_ARMOR;

    value = GetModifierValue(unitMod, BASE_VALUE);         // base armor (from items)
    value *= GetModifierValue(unitMod, BASE_PCT);           // armor percent from items
    value += GetStat(STAT_AGILITY) * 2.0f;                  // armor bonus from stats
    value += GetModifierValue(unitMod, TOTAL_VALUE);

    // add dynamic flat mods
    AuraList const& mResbyIntellect = GetAurasByType(SPELL_AURA_MOD_RESISTANCE_OF_STAT_PERCENT);
    for (AuraList::const_iterator i = mResbyIntellect.begin(); i != mResbyIntellect.end(); ++i)
    {
        Modifier* mod = (*i)->GetModifier();
        if (mod->m_miscvalue & SPELL_SCHOOL_MASK_NORMAL)
            value += int32(GetStat(Stats((*i)->GetMiscBValue())) * mod->m_amount / 100.0f);
    }

    value *= GetModifierValue(unitMod, TOTAL_PCT);

    SetArmor(int32(value));

    Pet* pet = GetPet();
    if (pet)
        pet->UpdateArmor();

    UpdateAttackPowerAndDamage();                           // armor dependent auras update for SPELL_AURA_MOD_ATTACK_POWER_OF_ARMOR
}

float Creature::GetHealthBonusFromStamina()
{
    float stamina = GetStat(STAT_STAMINA);

    float baseStam = stamina < 20 ? stamina : 20;
    float moreStam = stamina - baseStam;

    return baseStam + (moreStam * 10.0f);
}

float Creature::GetManaBonusFromIntellect()
{
    float intellect = GetStat(STAT_INTELLECT);

    float baseInt = intellect < 20 ? intellect : 20;
    float moreInt = intellect - baseInt;

    return baseInt + (moreInt * 15.0f);
}

void Creature::UpdateMaxHealth()
{
    UnitMods unitMod = UNIT_MOD_HEALTH;
    const float MonsterHealthTable[] = { 1.0f, 2.0f, 3.2f, 5.12f, 8.19f, 13.11f, 20.97f, 33.55f, 53.69f, 85.90f, 189.85f, 416.25f, 912.60f, 2000.82f };

    GameDifficulty gameDifficulty = sMapMgr.GetCurrentDifficulty();
    float healthBonus = MonsterHealthTable[gameDifficulty];

    //float value = GetModifierValue(unitMod, BASE_VALUE) + GetCreateHealth();
    //value *= GetModifierValue(unitMod, BASE_PCT);
    //value += GetModifierValue(unitMod, TOTAL_VALUE) + GetHealthBonusFromStamina();
    //value *= GetModifierValue(unitMod, TOTAL_PCT);
    float value = float(GetCreateHealth());

    SetMaxHealth((uint32)value * healthBonus);
}

void Creature::UpdateMaxPower(Powers power)
{
    UnitMods unitMod = UnitMods(UNIT_MOD_POWER_START + power);

    uint32 create_power = GetCreatePowers(power);

    // ignore classes without mana
    float bonusPower = (power == POWER_MANA && create_power > 0) ? GetManaBonusFromIntellect() : 0;

    float value = GetModifierValue(unitMod, BASE_VALUE) + create_power;
    value *= GetModifierValue(unitMod, BASE_PCT);
    value += GetModifierValue(unitMod, TOTAL_VALUE) + bonusPower;
    value *= GetModifierValue(unitMod, TOTAL_PCT);

    SetMaxPower(power, uint32(value));
}

void Creature::UpdateAttackPowerAndDamage(bool ranged)
{
    float val2 = 0.0f;
    float level = float(getLevel());

    uint32 _class = getClass();
    if (_class == 0) _class = CLASS_WARRIOR;

    UnitMods unitMod = ranged ? UNIT_MOD_ATTACK_POWER_RANGED : UNIT_MOD_ATTACK_POWER;

    uint16 index = UNIT_FIELD_ATTACK_POWER;
    uint16 index_mod = UNIT_FIELD_ATTACK_POWER_MODS;
    uint16 index_mult = UNIT_FIELD_ATTACK_POWER_MULTIPLIER;

    if (ranged)
    {
        index = UNIT_FIELD_RANGED_ATTACK_POWER;
        index_mod = UNIT_FIELD_RANGED_ATTACK_POWER_MODS;
        index_mult = UNIT_FIELD_RANGED_ATTACK_POWER_MULTIPLIER;

        switch (_class)
        {
            case CLASS_HUNTER: val2 = level * 2.0f + GetStat(STAT_AGILITY) - 10.0f;    break;
            case CLASS_ROGUE:  val2 = level + GetStat(STAT_AGILITY) - 10.0f;    break;
            case CLASS_WARRIOR: val2 = level + GetStat(STAT_AGILITY) - 10.0f;    break;
            case CLASS_DRUID:
                switch (GetShapeshiftForm())
                {
                    case FORM_CAT:
                    case FORM_BEAR:
                    case FORM_DIREBEAR:
                        val2 = 0.0f; break;
                    default:
                        val2 = GetStat(STAT_AGILITY) - 10.0f; break;
                }
                break;
            default: val2 = GetStat(STAT_AGILITY) - 10.0f; break;
        }
    }
    else
    {
        switch (_class)
        {
            case CLASS_WARRIOR:      val2 = level * 3.0f + GetStat(STAT_STRENGTH) * 2.0f - 20.0f; break;
            case CLASS_PALADIN:      val2 = level * 3.0f + GetStat(STAT_STRENGTH) * 2.0f - 20.0f; break;
            case CLASS_DEATH_KNIGHT: val2 = level * 3.0f + GetStat(STAT_STRENGTH) * 2.0f - 20.0f; break;
            case CLASS_ROGUE:        val2 = level * 2.0f + GetStat(STAT_STRENGTH) + GetStat(STAT_AGILITY) - 20.0f; break;
            case CLASS_HUNTER:       val2 = level * 2.0f + GetStat(STAT_STRENGTH) + GetStat(STAT_AGILITY) - 20.0f; break;
            case CLASS_SHAMAN:       val2 = level * 2.0f + GetStat(STAT_STRENGTH) + GetStat(STAT_AGILITY) - 20.0f; break;
            case CLASS_DRUID:
            {
                ShapeshiftForm form = GetShapeshiftForm();
                // Check if Predatory Strikes is skilled
                float mLevelBonus = 0.0f;
                float mBonusWeaponAtt = 0.0f;
                switch (form)
                {
                    case FORM_CAT:
                    case FORM_BEAR:
                    case FORM_DIREBEAR:
                    case FORM_MOONKIN:
                    {
                        Unit::AuraList const& mDummy = GetAurasByType(SPELL_AURA_DUMMY);
                        for (Unit::AuraList::const_iterator itr = mDummy.begin(); itr != mDummy.end(); ++itr)
                        {
                            if ((*itr)->GetSpellProto()->SpellIconID != 1563)
                                continue;

                            // Predatory Strikes (effect 0)
                            if ((*itr)->GetEffIndex() == EFFECT_INDEX_0 && IsInFeralForm())
                                mLevelBonus = getLevel() * (*itr)->GetModifier()->m_amount / 100.0f;
                            // Predatory Strikes (effect 1)
                            else if ((*itr)->GetEffIndex() == EFFECT_INDEX_1)
                                mBonusWeaponAtt = (*itr)->GetModifier()->m_amount;

                            if (mLevelBonus != 0.0f && mBonusWeaponAtt != 0.0f)
                                break;
                        }
                        break;
                    }
                    default: break;
                }

                switch (form)
                {
                    case FORM_CAT:
                        val2 = GetStat(STAT_STRENGTH) * 2.0f + GetStat(STAT_AGILITY) - 20.0f + mLevelBonus + mBonusWeaponAtt; break;
                    case FORM_BEAR:
                    case FORM_DIREBEAR:
                        val2 = GetStat(STAT_STRENGTH) * 2.0f - 20.0f + mLevelBonus + mBonusWeaponAtt; break;
                    case FORM_MOONKIN:
                        val2 = GetStat(STAT_STRENGTH) * 2.0f - 20.0f + mBonusWeaponAtt; break;
                    default:
                        val2 = GetStat(STAT_STRENGTH) * 2.0f - 20.0f; break;
                }
                break;
            }
            case CLASS_MAGE:    val2 = GetStat(STAT_STRENGTH) - 10.0f; break;
            case CLASS_PRIEST:  val2 = GetStat(STAT_STRENGTH) - 10.0f; break;
            case CLASS_WARLOCK: val2 = GetStat(STAT_STRENGTH) - 10.0f; break;
        }
    }

    SetModifierValue(unitMod, BASE_VALUE, val2);

    float base_attPower = GetModifierValue(unitMod, BASE_VALUE) * GetModifierValue(unitMod, BASE_PCT);
    float attPowerMod = GetModifierValue(unitMod, TOTAL_VALUE);

    // add dynamic flat mods
    if (ranged)
    {
        if ((getClassMask() & CLASSMASK_WAND_USERS) == 0)
        {
            AuraList const& mRAPbyStat = GetAurasByType(SPELL_AURA_MOD_RANGED_ATTACK_POWER_OF_STAT_PERCENT);
            for (AuraList::const_iterator i = mRAPbyStat.begin(); i != mRAPbyStat.end(); ++i)
                attPowerMod += int32(GetStat(Stats((*i)->GetModifier()->m_miscvalue)) * (*i)->GetModifier()->m_amount / 100.0f);
        }
    }
    else
    {
        AuraList const& mAPbyStat = GetAurasByType(SPELL_AURA_MOD_ATTACK_POWER_OF_STAT_PERCENT);
        for (AuraList::const_iterator i = mAPbyStat.begin(); i != mAPbyStat.end(); ++i)
            attPowerMod += int32(GetStat(Stats((*i)->GetModifier()->m_miscvalue)) * (*i)->GetModifier()->m_amount / 100.0f);

        AuraList const& mAPbyArmor = GetAurasByType(SPELL_AURA_MOD_ATTACK_POWER_OF_ARMOR);
        for (AuraList::const_iterator iter = mAPbyArmor.begin(); iter != mAPbyArmor.end(); ++iter)
            // always: ((*i)->GetModifier()->m_miscvalue == 1 == SPELL_SCHOOL_MASK_NORMAL)
            attPowerMod += int32(GetArmor() / (*iter)->GetModifier()->m_amount);
    }

    float attPowerMultiplier = GetModifierValue(unitMod, TOTAL_PCT) - 1.0f;

    SetInt32Value(index, (uint32)base_attPower);            // UNIT_FIELD_(RANGED)_ATTACK_POWER field
    SetInt32Value(index_mod, (uint32)attPowerMod);          // UNIT_FIELD_(RANGED)_ATTACK_POWER_MODS field
    SetFloatValue(index_mult, attPowerMultiplier);          // UNIT_FIELD_(RANGED)_ATTACK_POWER_MULTIPLIER field

                                                            // automatically update weapon damage after attack power modification
    if (ranged)
    {
        UpdateDamagePhysical(RANGED_ATTACK);

        Pet* pet = GetPet();                                // update pet's AP
        if (pet)
            pet->UpdateAttackPowerAndDamage();
    }
    else
    {
        UpdateDamagePhysical(BASE_ATTACK);
        if (haveOffhandWeapon())          // allow update offhand damage only if player knows DualWield Spec and has equipped offhand weapon
            UpdateDamagePhysical(OFF_ATTACK);
    }
}

void Creature::CalculateMinMaxDamage(WeaponAttackType attType, bool normalized, float& min_damage, float& max_damage)
{
    const float MonsterDamage[] = { 1.0f, 1.3f, 1.89f, 2.73f, 3.96f, 5.75f, 8.33f, 12.08f, 17.52f, 25.40f, 36.04f, 50.97f, 72.08f, 101.94f };

    GameDifficulty gameDifficulty = sMapMgr.GetCurrentDifficulty();
    float damageBonus = MonsterDamage[gameDifficulty];
    float level = float(getLevel());
    float hp = float(GetMaxHealth());

    min_damage = (1.4873f *  log(level) - 0.1681f) / level * hp * damageBonus;
    max_damage = (2.6312f *  log(level) - 0.6672f) / level * hp * damageBonus;
    if (min_damage <= 0.0f)
    {
        min_damage = MINDAMAGE;
        max_damage = MAXDAMAGE;
    }

    //UnitMods unitMod;
    //UnitMods attPower;

    //switch (attType)
    //{
    //    case BASE_ATTACK:
    //    default:
    //        unitMod = UNIT_MOD_DAMAGE_MAINHAND;
    //        attPower = UNIT_MOD_ATTACK_POWER;
    //        break;
    //    case OFF_ATTACK:
    //        unitMod = UNIT_MOD_DAMAGE_OFFHAND;
    //        attPower = UNIT_MOD_ATTACK_POWER;
    //        break;
    //    case RANGED_ATTACK:
    //        unitMod = UNIT_MOD_DAMAGE_RANGED;
    //        attPower = UNIT_MOD_ATTACK_POWER_RANGED;
    //        break;
    //}

    //float att_speed = GetAPMultiplier(attType, normalized);

    //float base_value = GetModifierValue(unitMod, BASE_VALUE) + GetTotalAttackPowerValue(attType) / 14.0f * att_speed;
    //float base_pct = GetModifierValue(unitMod, BASE_PCT);
    //float total_value = GetModifierValue(unitMod, TOTAL_VALUE);
    //float total_pct = GetModifierValue(unitMod, TOTAL_PCT);

    //float weapon_mindamage = GetWeaponDamageRange(attType, MINDAMAGE);
    //float weapon_maxdamage = GetWeaponDamageRange(attType, MAXDAMAGE);

    //if (IsInFeralForm())                                    // check if player is druid and in cat or bear forms, non main hand attacks not allowed for this mode so not check attack type
    //{
    //    uint32 lvl = getLevel();
    //    if (lvl > 60)
    //        lvl = 60;

    //    weapon_mindamage = lvl * 0.85f * att_speed;
    //    weapon_maxdamage = lvl * 1.25f * att_speed;
    //}
    //else if (!CanUseEquippedWeapon(attType))                // check if player not in form but still can't use weapon (broken/etc)
    //{
    //    weapon_mindamage = BASE_MINDAMAGE;
    //    weapon_maxdamage = BASE_MAXDAMAGE;
    //}
    //else if (attType == RANGED_ATTACK)                      // add ammo DPS to ranged damage
    //{
    //    const float noAmmoDpf = 0.0f;
    //    weapon_mindamage += noAmmoDpf * att_speed;
    //    weapon_maxdamage += noAmmoDpf * att_speed;
    //}

    //min_damage = ((base_value + weapon_mindamage) * base_pct + total_value) * total_pct * damageBonus;
    //max_damage = ((base_value + weapon_maxdamage) * base_pct + total_value) * total_pct * damageBonus;
}

void Creature::UpdateDamagePhysical(WeaponAttackType attType)
{
    float mindamage;
    float maxdamage;

    CalculateMinMaxDamage(attType, false, mindamage, maxdamage);

    switch (attType)
    {
        case BASE_ATTACK:
        default:
            SetStatFloatValue(UNIT_FIELD_MINDAMAGE, mindamage);
            SetStatFloatValue(UNIT_FIELD_MAXDAMAGE, maxdamage);
            break;
        case OFF_ATTACK:
            SetStatFloatValue(UNIT_FIELD_MINOFFHANDDAMAGE, mindamage);
            SetStatFloatValue(UNIT_FIELD_MAXOFFHANDDAMAGE, maxdamage);
            break;
        case RANGED_ATTACK:
            SetStatFloatValue(UNIT_FIELD_MINRANGEDDAMAGE, mindamage);
            SetStatFloatValue(UNIT_FIELD_MAXRANGEDDAMAGE, maxdamage);
            break;
    }
}

void Creature::UpdateManaRegen()
{
    float Intellect = GetStat(STAT_INTELLECT);
    // Mana regen from spirit and intellect
    float power_regen = sqrt(Intellect) * OCTRegenMPPerSpirit();
    // Apply PCT bonus from SPELL_AURA_MOD_POWER_REGEN_PERCENT aura on spirit base regen
    power_regen *= GetTotalAuraMultiplierByMiscValue(SPELL_AURA_MOD_POWER_REGEN_PERCENT, POWER_MANA);

    // Mana regen from SPELL_AURA_MOD_POWER_REGEN aura
    int32 m_baseManaRegen = 0;
    float power_regen_mp5 = (GetTotalAuraModifierByMiscValue(SPELL_AURA_MOD_POWER_REGEN, POWER_MANA) + m_baseManaRegen) / 5.0f;

    // Get bonus from SPELL_AURA_MOD_MANA_REGEN_FROM_STAT aura
    AuraList const& regenAura = GetAurasByType(SPELL_AURA_MOD_MANA_REGEN_FROM_STAT);
    for (AuraList::const_iterator i = regenAura.begin(); i != regenAura.end(); ++i)
    {
        Modifier* mod = (*i)->GetModifier();
        power_regen_mp5 += GetStat(Stats(mod->m_miscvalue)) * mod->m_amount / 500.0f;
    }

    // Set regen rate in cast state apply only on spirit based regen
    int32 modManaRegenInterrupt = GetTotalAuraModifier(SPELL_AURA_MOD_MANA_REGEN_INTERRUPT);
    if (modManaRegenInterrupt > 100)
        modManaRegenInterrupt = 100;
    SetStatFloatValue(UNIT_FIELD_POWER_REGEN_INTERRUPTED_FLAT_MODIFIER, power_regen_mp5 + power_regen * modManaRegenInterrupt / 100.0f);

    SetStatFloatValue(UNIT_FIELD_POWER_REGEN_FLAT_MODIFIER, power_regen_mp5 + power_regen);
}

float Creature::OCTRegenMPPerSpirit()
{
    uint32 level = getLevel();
    uint32 _class = getClass();
    if (_class == 0) _class = CLASS_WARRIOR;

    if (level > GT_MAX_LEVEL) level = GT_MAX_LEVEL;

    GtRegenMPPerSptEntry  const* moreRatio = sGtRegenMPPerSptStore.LookupEntry((_class - 1) * GT_MAX_LEVEL + level - 1);
    if (moreRatio == nullptr)
        return 0.0f;

    // Formula get from PaperDollFrame script
    float spirit = GetStat(STAT_SPIRIT);
    float regen = spirit * moreRatio->ratio;
    return regen;
}

void Creature::InitStatsForLevel()
{
    uint32 _class = getClass();
    //if (_class == 0) _class = CLASS_WARRIOR;

    uint32 race = getRace();
    //if (race == 0) race = RACE_HUMAN;

    PlayerClassLevelInfo classInfo;
    sObjectMgr.GetPlayerClassLevelInfo(_class, getLevel(), &classInfo);

    PlayerLevelInfo info;
    sObjectMgr.GetPlayerLevelInfo(race, _class, getLevel(), &info);

    // reset before any aura state sources (health set/aura apply)
    SetUInt32Value(UNIT_FIELD_AURASTATE, 0);

    // set default cast time multiplier
    SetFloatValue(UNIT_MOD_CAST_SPEED, 1.0f);

    // save base values (bonuses already included in stored stats
    //for (int i = STAT_STRENGTH; i < MAX_STATS; ++i)
    //    SetCreateStat(Stats(i), info.stats[i]);

    //for (int i = STAT_STRENGTH; i < MAX_STATS; ++i)
    //    SetStat(Stats(i), info.stats[i]);

    float level = float(getLevel());
    uint32 basehealth = uint32(3.7f * exp(level / 10.0f) * level);
    //classInfo.basehealth
    SetCreateHealth(basehealth);

    // set create powers
    SetCreateMana(classInfo.basemana);

    SetArmor(int32(m_createStats[STAT_AGILITY] * 2));

    InitStatBuffMods();

    // reset attack power, damage and attack speed fields
    SetFloatValue(UNIT_FIELD_BASEATTACKTIME, 2000.0f);
    SetFloatValue(UNIT_FIELD_BASEATTACKTIME + 1, 2000.0f);  // offhand attack time
    SetFloatValue(UNIT_FIELD_RANGEDATTACKTIME, 2000.0f);

    SetFloatValue(UNIT_FIELD_MINDAMAGE, 0.0f);
    SetFloatValue(UNIT_FIELD_MAXDAMAGE, 0.0f);
    SetFloatValue(UNIT_FIELD_MINOFFHANDDAMAGE, 0.0f);
    SetFloatValue(UNIT_FIELD_MAXOFFHANDDAMAGE, 0.0f);
    SetFloatValue(UNIT_FIELD_MINRANGEDDAMAGE, 0.0f);
    SetFloatValue(UNIT_FIELD_MAXRANGEDDAMAGE, 0.0f);

    SetInt32Value(UNIT_FIELD_ATTACK_POWER, 0);
    SetInt32Value(UNIT_FIELD_ATTACK_POWER_MODS, 0);
    SetFloatValue(UNIT_FIELD_ATTACK_POWER_MULTIPLIER, 0.0f);
    SetInt32Value(UNIT_FIELD_RANGED_ATTACK_POWER, 0);
    SetInt32Value(UNIT_FIELD_RANGED_ATTACK_POWER_MODS, 0);
    SetFloatValue(UNIT_FIELD_RANGED_ATTACK_POWER_MULTIPLIER, 0.0f);

    // set armor (resistance 0) to original value (create_agility*2)
    SetArmor(int32(m_createStats[STAT_AGILITY] * 2));
    SetResistanceBuffMods(SpellSchools(0), true, 0.0f);
    SetResistanceBuffMods(SpellSchools(0), false, 0.0f);
    // set other resistance to original value (0)
    for (int i = 1; i < MAX_SPELL_SCHOOL; ++i)
    {
        SetResistance(SpellSchools(i), 0);
        SetResistanceBuffMods(SpellSchools(i), true, 0.0f);
        SetResistanceBuffMods(SpellSchools(i), false, 0.0f);
    }

    for (int i = 0; i < MAX_SPELL_SCHOOL; ++i)
    {
        SetUInt32Value(UNIT_FIELD_POWER_COST_MODIFIER + i, 0);
        SetFloatValue(UNIT_FIELD_POWER_COST_MULTIPLIER + i, 0.0f);
    }

    // save new stats
    for (int i = POWER_MANA; i < MAX_POWERS; ++i)
        SetMaxPower(Powers(i), GetCreatePowers(Powers(i)));

    SetMaxHealth(basehealth);                     // stamina bonus will applied later

                                                            // cleanup mounted state (it will set correctly at aura loading if player saved at mount.
    SetUInt32Value(UNIT_FIELD_MOUNTDISPLAYID, 0);

    //// cleanup unit flags (will be re-applied if need at aura load).
    //RemoveFlag(UNIT_FIELD_FLAGS,
    //    UNIT_FLAG_NON_ATTACKABLE | UNIT_FLAG_DISABLE_MOVE | UNIT_FLAG_NOT_ATTACKABLE_1 |
    //    UNIT_FLAG_OOC_NOT_ATTACKABLE | UNIT_FLAG_PASSIVE | UNIT_FLAG_LOOTING |
    //    UNIT_FLAG_PET_IN_COMBAT | UNIT_FLAG_SILENCED | UNIT_FLAG_PACIFIED |
    //    UNIT_FLAG_STUNNED | UNIT_FLAG_IN_COMBAT | UNIT_FLAG_DISARMED |
    //    UNIT_FLAG_CONFUSED | UNIT_FLAG_FLEEING | UNIT_FLAG_NOT_SELECTABLE |
    //    UNIT_FLAG_SKINNABLE | UNIT_FLAG_MOUNT | UNIT_FLAG_TAXI_FLIGHT);
    //SetFlag(UNIT_FIELD_FLAGS, UNIT_FLAG_PVP_ATTACKABLE);    // must be set

    //SetFlag(UNIT_FIELD_FLAGS_2, UNIT_FLAG2_REGENERATE_POWER); // must be setv

    RemoveStandFlags(UNIT_STAND_FLAGS_ALL);                 // one form stealth modified bytes
    RemoveByteFlag(UNIT_FIELD_BYTES_2, 1, UNIT_BYTE2_FLAG_FFA_PVP | UNIT_BYTE2_FLAG_SANCTUARY);

    // set current level health and mana/energy to maximum after applying all mods.
    if (!this->isInCombat())
    {
        this->SetHealth(GetMaxHealth());
    }

    SetModifierValue(UNIT_MOD_HEALTH, BASE_VALUE, float(GetMaxHealth()));

    SetPower(POWER_MANA, GetMaxPower(POWER_MANA));
    SetModifierValue(UnitMods(UNIT_MOD_POWER_START + POWER_MANA), BASE_VALUE, float(GetMaxPower(POWER_MANA)));

    SetPower(POWER_ENERGY, GetMaxPower(POWER_ENERGY));
    SetModifierValue(UnitMods(UNIT_MOD_POWER_START + POWER_ENERGY), BASE_VALUE, float(GetMaxPower(POWER_ENERGY)));

    if (GetPower(POWER_RAGE) > GetMaxPower(POWER_RAGE))
        SetPower(POWER_RAGE, GetMaxPower(POWER_RAGE));
    SetModifierValue(UnitMods(UNIT_MOD_POWER_START + POWER_RAGE), BASE_VALUE, float(GetMaxPower(POWER_RAGE)));

    SetPower(POWER_FOCUS, 0);
    SetModifierValue(UnitMods(UNIT_MOD_POWER_START + POWER_FOCUS), BASE_VALUE, float(0));

    SetPower(POWER_HAPPINESS, 0);
    SetModifierValue(UnitMods(UNIT_MOD_POWER_START + POWER_HAPPINESS), BASE_VALUE, float(0));

    SetPower(POWER_RUNIC_POWER, 0);
    SetModifierValue(UnitMods(UNIT_MOD_POWER_START + POWER_RUNIC_POWER), BASE_VALUE, float(0));

    // update level to hunter/summon pet
    if (Pet* pet = GetPet())
        pet->SynchronizeLevelWithOwner();
}


bool Creature::CanBeModded() const
{
    return !this->IsTemporarySummon() && !this->IsWorldBoss() && this->GetUInt32Value(UNIT_NPC_FLAGS) == UNIT_NPC_FLAG_NONE && this->IsHostileToPlayers() && !sObjectMgr.IsUniqueCreature(GetCreatureInfo()->Entry);
}

void Creature::SetEliteIfChosen()
{
    if (this->CanBeModded())
    {
        bool isElite = urand(1, 5) == 1;
        if (isElite)
        {
            this->SetObjectScale(this->GetObjectScale() * 1.5f);
            //this->SetResistance();
        }
    }
}

static float summonPositionsX[] = { 0.0f, ATTACK_DISTANCE, -ATTACK_DISTANCE, ATTACK_DISTANCE, -ATTACK_DISTANCE };
static float summonPositionsY[] = { 0.0f, ATTACK_DISTANCE, ATTACK_DISTANCE, -ATTACK_DISTANCE, -ATTACK_DISTANCE };

void Creature::SummonCreaturePool()
{
    if (this->CanBeModded())
    {
        for (uint32 i = 0; i < urand(0, 4); i++)
        {
            Creature* creature = this->SummonCreature(GetCreatureInfo()->Entry, this->GetPositionX() + summonPositionsX[i], this->GetPositionY() + summonPositionsY[i], this->GetPositionZ(), 0.0, TEMPSUMMON_DEAD_DESPAWN, 0);
        }
    }
}
