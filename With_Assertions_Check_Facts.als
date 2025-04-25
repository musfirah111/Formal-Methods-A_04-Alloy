
one sig NationalHolidays {
  dates: set String
}
abstract sig CaseStatus {}
one sig Open, Closed extends CaseStatus {}

abstract sig Person {
  id: one String,
  name: one String,
  email: one String,
  phoneNumber: one Int,
  dob: one String,
  gender: one String
}

sig Patient extends Person {
  prescription: some Prescription,
  appointment: some Appointment,
  bill: some Bill,
  ehr: one EHR,
  dischargeSummary: lone DischargeSummary,
  bed: lone Bed,
  caseStatus: one CaseStatus
}

sig Staff extends Person {
  type: one String,
  isOnLeave: one Int,
  qualification: some String,
  assignedShifts: set Shift
}

sig Doctor extends Staff {
  maxAppointmentsPerDay: one Int,
  rank: one String,
  appointments: set Appointment
}

sig Appointment {
  id: one String,
  type: one String,
  date: one String,
  status: one String,
  doctor: one Doctor,
  patient: one Patient,
  resources: some Resource,
  labTests: some LabTest,
  remainder: lone Remainder,
  timeSlot: one TimeSlot
}

sig Prescription {
  id: one String,
  medicines: some Medicine,
  appointment: one Appointment
}

sig Bill {
  totalAmount: one Int,
  isPaid: one Int,
  appointment: one Appointment
}

sig LabTest {
  id: one Int,
  appointment: one Appointment,
  testCost: one Int
}

sig EHR {
  id: one Int,
  dateCreated: one String,
  currentMedications: set Medicine,
  pastSurgeries: set Surgery,
  labTests: set LabTest,
  allergies: set Allergy,
  patient: one Patient,
  receivedtreatment: one Int
}

sig Bed {
  id: one Int,
  location: one String,
  isOccupied: one Int,
  assignedPatient: lone Patient,
  type: one String //"General Ward", "ICU", "CCU"
}

sig Surgery {
  id: one Int,
  anesthetist: one Staff,
  assignedOT: one Int,
  appointment: one Appointment
}

sig DischargeSummary {
  summaryID: one Int,
  dischargeDate: one String,
  status: one String,
  signedBy: one Doctor,
  patient: one Patient
}

sig Pharmacy {
  medicines: some Medicine
}

sig Medicine {
  id: one String,
  name: one String,
  stock: one Int,
  threshold: one Int,
  allergens: set String,
  medicineCost: one Int
}

sig Allergy {
  allergyID: one String,
  name: one String,
  severity: one String,
  reaction: lone String,
  isClinicallyConfirmed: one Int,
  identificationDate: lone String
}

sig Resource {
  type: one String,
  isAvailable: one Int,
  resourceCost: one Int,
  appointment: one Appointment
}

sig Shift {
  id: one Int,
  date: one String,
  type: one String,  //Doctor, Nurse, QualityAssuranceTeam
  location: one String, 
  startingTime: one Time,
  endingTime: one Time,
  timeSlot: set TimeSlot,
  assignedTo: set Staff
}

sig TimeSlot {
  startingTime: one Time,
  endingTime: one Time
}

// Time.
sig Time {
  hour: one Int,
  minute: one Int
}

sig OperationTheater {
  id: one Int
}

sig Remainder {
  id: one Int,
  sentTime: one Time,
  remainderOfAppointment: one Appointment
}


sig Feedback {
  id: one Int,
  rating: one Int,
  comment: lone String,
  appointment: one Appointment,
  notifiedTeam: set Staff // Relation to staff of type "QualityAssuranceTeam"
}

sig LowStockAlert {
  medicine: one Medicine,
  generatedOn: one String,
  sentTo: one Staff
}


fun timeInMinutes[t: Time]: Int {
  mul[t.hour, 60] + t.minute
}


//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Simple Structural>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

// 1. A doctor can be assigned to multiple patients.
fact DoctorCanHaveMultiplePatients {
  all d: Doctor |
    #({ p: Patient | some a: d.appointments | a.patient = p }) > 1
}

// Assertion
assert DoctorCanHaveMultiplePatientsAssertion {
  all d: Doctor |
    #({ p: Patient | some a: d.appointments | a.patient = p }) > 1
}
check DoctorCanHaveMultiplePatientsAssertion for 5

//2. A resource can be assigned to only one patient at a time.
fact EachResourceAssignedToOnePatient {
  all r: Resource |
    one r.appointment.patient
}

// Assertion to ensure no two resources are assigned to the same patient at the same time.
assert ResourceAssignedToOnePatientAssertion {
  all r: Resource |
    one r.appointment.patient
}

check ResourceAssignedToOnePatientAssertion for 5

// 3. Each appointment is linked to one doctor and one patient.
fact EachAppointmentLinkedToDoctorAndPatient {
  all a: Appointment |
    one a.doctor and one a.patient
}

// Assertion.
assert EachAppointmentLinkedToDoctorAndPatient {
  all a: Appointment |
    one a.doctor and one a.patient
}
check EachAppointmentLinkedToDoctorAndPatient for 5

// 4. Each prescription is issued by a registered doctor.
fact PrescriptionsAreIssuedByDoctors {
  all p: Prescription |
    one p.appointment.doctor
}

// Assertion.
assert PrescriptionsAreIssuedByDoctorsAssertion {
  all p: Prescription |
    one p.appointment.doctor
}
check PrescriptionsAreIssuedByDoctorsAssertion for 5

// 5. Every bill corresponds to a single patient.
fact BillLinkedToOnePatient {
  all b: Bill | one b.appointment.patient
}

// Assertion.
assert BillLinkedToOnePatientAssertion {
  all b: Bill |
    one b.appointment.patient
}
check BillLinkedToOnePatientAssertion for 5

//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Moderate Logic Rules>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

//1. Appointments are only allowed if a doctor is available.
fact AppointmentAllowedOnlyIfDoctorAvailable {
  all a: Appointment |
    some s: a.doctor.assignedShifts | s.date = a.date
}

// Assertion for AppointmentAllowedOnlyIfDoctorAvailable
assert AppointmentAllowedOnlyIfDoctorAvailableAssertion {
  all a: Appointment |
    some s: a.doctor.assignedShifts | s.date = a.date
}
check AppointmentAllowedOnlyIfDoctorAvailableAssertion for 5

//2. If a patient cancels an appointment, the time slot should become available again.
fact CancelledAppointmentFreesTimeSlot {
  all ts: TimeSlot |
    some a: Appointment | a.status = "cancelled" and a.timeSlot = ts =>
      all a2: Appointment | a2.timeSlot = ts implies a2.status = "cancelled"
}

// Assertion for CancelledAppointmentFreesTimeSlot
assert CancelledAppointmentFreesTimeSlotAssertion {
  all ts: TimeSlot |
    some a: Appointment | a.status = "cancelled" and a.timeSlot = ts =>
      all a2: Appointment | a2.timeSlot = ts implies a2.status = "cancelled"
}
check CancelledAppointmentFreesTimeSlotAssertion for 5

//3. If the medicine stock is less than the minimum threshold, notify the pharmacy admin.
fact GenerateAlertWhenStockLow {
  all m: Medicine |
    m.stock < m.threshold =>
      some a: LowStockAlert |
        a.medicine = m and
        some s: Staff |
          s.type = "PharmacyAdmin" and
          a.sentTo = s
}

// Assertion for GenerateAlertWhenStockLow
assert GenerateAlertWhenStockLowAssertion {
  all m: Medicine |
    m.stock < m.threshold =>
      some a: LowStockAlert |
        a.medicine = m and
        some s: Staff |
          s.type = "PharmacyAdmin" and
          a.sentTo = s
}
check GenerateAlertWhenStockLowAssertion for 5


//4. If a staff member is marked on leave, they cannot be assigned to duties that day.
fact StaffOnLeaveNotAssignedToShifts {
  all s: Staff |
    s.isOnLeave = 1 =>
      all sh: Shift |
        sh in s.assignedShifts implies no sh
}

// Assertion for StaffOnLeaveNotAssignedToShifts
assert StaffOnLeaveNotAssignedToShiftsAssertion {
  all s: Staff |
    s.isOnLeave = 1 =>
      all sh: Shift |
        sh in s.assignedShifts implies no sh
}
check StaffOnLeaveNotAssignedToShiftsAssertion for 5

//5. If the doctor has more than 25 patients in a day, no further appointments can be scheduled.
fact PerDayMax25PatientsPerDoctor {
  all d: Doctor, day: String |
    #({ a: Appointment | a.doctor = d and a.date = day }.patient) <= 25
}

// Assertion for PerDayMax25PatientsPerDoctor
assert PerDayMax25PatientsPerDoctorAssertion {
  all d: Doctor, day: String |
    #({ a: Appointment | a.doctor = d and a.date = day }.patient) <= 25
}
check PerDayMax25PatientsPerDoctorAssertion for 5

//6. Feedback can only be submitted after the appointment status is “Completed.”
fact FeedbackOnlyAfterCompletedAppointment {
  all f: Feedback |
    f.appointment.status = "Completed"
}

// Assertion for FeedbackOnlyAfterCompletedAppointment
assert FeedbackOnlyAfterCompletedAppointmentAssertion {
  all f: Feedback |
    f.appointment.status = "Completed"
}
check FeedbackOnlyAfterCompletedAppointmentAssertion for 5

//7. Appointment reminders must be sent 24 hours before the scheduled time.
fact remainderForAppointment {
  all a: Appointment | 
    some a.remainder => {
      let r = a.remainder,
          apptTime = a.timeSlot.startingTime,
          sentTime = r.sentTime |
        apptTime.hour - sentTime.hour = 24 and
        apptTime.minute = sentTime.minute
    }
}

// Assertion for remainderForAppointment
assert remainderForAppointmentAssertion {
  all a: Appointment | 
    some a.remainder => {
      let r = a.remainder,
          apptTime = a.timeSlot.startingTime,
          sentTime = r.sentTime |
        apptTime.hour - sentTime.hour = 24 and
        apptTime.minute = sentTime.minute
    }
}
check remainderForAppointmentAssertion for 5

//8. If a patient receives any treatment, then a billing entry must be automatically generated for the services used.
fact automaticBillGeneration {
  all p: Patient |
    all a: p.appointment |
      one e: EHR | e.patient = p and e.receivedtreatment = 1 implies
        some b: Bill | b.appointment = a
}

// Assertion for automaticBillGeneration
assert automaticBillGenerationAssertion {
  all p: Patient |
    all a: p.appointment |
      one e: EHR | e.patient = p and e.receivedtreatment = 1 implies
        some b: Bill | b.appointment = a
}
check automaticBillGenerationAssertion for 5

//9. Discharge summary must be uploaded before closing a patient case file.
fact DischargeSummaryBeforeCaseClosure {
  all p: Patient |
    p.caseStatus = Closed implies p.dischargeSummary != none and p.dischargeSummary.patient = p
}

// Assertion for DischargeSummaryBeforeCaseClosure
assert DischargeSummaryBeforeCaseClosureAssertion {
  all p: Patient |
    p.caseStatus = Closed implies p.dischargeSummary != none and p.dischargeSummary.patient = p
}
check DischargeSummaryBeforeCaseClosureAssertion for 5

//10. If a patient is assigned to the ICU, the system must auto-assign a nurse.
fact AutoAssignedNurseToICUPatient {
  all p: Patient |
    p.bed.isOccupied = 1 and p.bed.location = "ICU" implies
      some n: Staff |
        n.type = "Nurse" and
        some s: n.assignedShifts |
          s.date = p.appointment.date and
          s.location = "ICU"
}

// Assertion for AutoAssignedNurseToICUPatient
assert AutoAssignedNurseToICUPatientAssertion {
  all p: Patient |
    p.bed.isOccupied = 1 and p.bed.location = "ICU" implies
      some n: Staff |
        n.type = "Nurse" and
        some s: n.assignedShifts |
          s.date = p.appointment.date and
          s.location = "ICU"
}
check AutoAssignedNurseToICUPatientAssertion for 5

// <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< Complex. >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

// 1. No two appointments for the same doctor can overlap in time.
fact NoOverlappingAppointments {
  all a1, a2: Appointment |
    (a1 != a2 and a1.doctor = a2.doctor) implies (
      a1.date != a2.date or
      timeInMinutes[a1.timeSlot.endingTime] <= timeInMinutes[a2.timeSlot.startingTime] or
      timeInMinutes[a2.timeSlot.endingTime] <= timeInMinutes[a1.timeSlot.startingTime])
}

// Assertion to verify that no two appointments for the same doctor overlap in time
assert NoOverlappingAppointmentsAssertion {
  all a1, a2: Appointment |
    (a1 != a2 and a1.doctor = a2.doctor) implies (
      a1.date != a2.date or
      timeInMinutes[a1.timeSlot.endingTime] <= timeInMinutes[a2.timeSlot.startingTime] or
      timeInMinutes[a2.timeSlot.endingTime] <= timeInMinutes[a1.timeSlot.startingTime])
}
check NoOverlappingAppointmentsAssertion for 5

// 2. Doctors must not have back-to-back appointments without a 10-minute gap
fact DoctorAppointmentsHave10MinGap {
  all a1, a2: Appointment |
    (a1 != a2 and a1.doctor = a2.doctor and a1.date = a2.date) implies
      timeInMinutes[a1.timeSlot.endingTime] + 10 <= timeInMinutes[a2.timeSlot.startingTime]
      or timeInMinutes[a2.timeSlot.endingTime] + 10 <= timeInMinutes[a1.timeSlot.startingTime]
}

// Assertion to verify that doctors have a 10-minute gap between appointments
assert DoctorAppointmentsHave10MinGapAssertion {
  all a1, a2: Appointment |
    (a1 != a2 and a1.doctor = a2.doctor and a1.date = a2.date) implies
      timeInMinutes[a1.timeSlot.endingTime] + 10 <= timeInMinutes[a2.timeSlot.startingTime]
      or timeInMinutes[a2.timeSlot.endingTime] + 10 <= timeInMinutes[a1.timeSlot.startingTime]
}
check DoctorAppointmentsHave10MinGapAssertion for 5

// 3. Appointments must fall within the doctor’s declared working hours.
fact AppointmentsInDoctorsWorkingHours {
    all a: Appointment |
    some s: a.doctor.assignedShifts | (s.date = a.date) implies
    (timeInMinutes[a.timeSlot.startingTime] >= timeInMinutes[s.startingTime] and
    timeInMinutes[a.timeSlot.endingTime] <= timeInMinutes[s.endingTime])
}

// Assertion to verify that appointments fall within doctors' working hours
assert AppointmentsInDoctorsWorkingHoursAssertion {
    all a: Appointment |
    some s: a.doctor.assignedShifts | (s.date = a.date) implies
    (timeInMinutes[a.timeSlot.startingTime] >= timeInMinutes[s.startingTime] and
    timeInMinutes[a.timeSlot.endingTime] <= timeInMinutes[s.endingTime])
}
check AppointmentsInDoctorsWorkingHoursAssertion for 5

// 4. A nurse cannot be scheduled for night and morning shifts on the same day.
fact NoMorningAndNightShiftForSameNurse {
  all s1, s2: Shift |
    s1 != s2 and // different shifts.
    s1.date = s2.date and // same date.
    ((s1.type = "Morning" and s2.type = "Night") or (s1.type = "Night" and s2.type = "Morning")) implies
      no nurse: Staff | // no staff exists ...
        nurse.type = "Nurse" and // who is a nurse and ...
        nurse in s1.assignedTo and 
        nurse in s2.assignedTo // ... is assigned to both shifts.
}

// Assertion to verify that nurses cannot be scheduled for both morning and night shifts on the same day
assert NoMorningAndNightShiftForSameNurseAssertion {
  all s1, s2: Shift |
    s1 != s2 and // different shifts
    s1.date = s2.date and // same date
    ((s1.type = "Morning" and s2.type = "Night") or (s1.type = "Night" and s2.type = "Morning")) implies
      no nurse: Staff | // no staff exists ...
        nurse.type = "Nurse" and // who is a nurse and ...
        nurse in s1.assignedTo and 
        nurse in s2.assignedTo // ... is assigned to both shifts
}
check NoMorningAndNightShiftForSameNurseAssertion for 5


// 5. A patient’s EHR can only be modified by the assigned doctor.
fact OnlyAssignedDoctorCanModifyEHR {
  all a: Appointment |
    a.patient.ehr.patient = a.patient and
    a.doctor in Doctor
}

// Assertion to verify that only assigned doctors can modify EHR
assert OnlyAssignedDoctorCanModifyEHRAssertion {
  all a: Appointment |
    a.patient.ehr.patient = a.patient and
    a.doctor in Doctor
}
check OnlyAssignedDoctorCanModifyEHRAssertion for 5

// 6. If a patient is transferred from the ward to the ICU, the previous bed must be released.
fact BedReleaseWhenPatientTransferredAndBedType {
  all p: Patient, b1, b2: Bed |
    // Ensure patient p occupies b1 and b2 is empty.
    p.bed = b1 and b2.isOccupied = 0 and
    // When patient is transferred to b2 (ICU), b1 is released (ward).
    p.bed = b2 implies {
      // Ensure that the patient's previous bed is a ward bed (b1 type).
      b1.type = "General Ward" and
      b2.type = "ICU" and // The new bed is ICU.
      b1.isOccupied = 0 and  // Release previous bed.
      b1.assignedPatient = none and  // No longer assigned to any patient.
      b2.isOccupied = 1 and  // The new bed must be occupied.
      b2.assignedPatient = p // The patient is assigned to the new bed.
    }
}

// Assertion to verify bed release when patient is transferred to ICU
assert BedReleaseWhenPatientTransferredAndBedTypeAssertion {
  all p: Patient, b1, b2: Bed |
    // Ensure patient p occupies b1 and b2 is empty
    p.bed = b1 and b2.isOccupied = 0 and
    // When patient is transferred to b2 (ICU), b1 is released (ward)
    p.bed = b2 implies {
      // Ensure that the patient's previous bed is a ward bed (b1 type)
      b1.type = "General Ward" and
      b2.type = "ICU" and // The new bed is ICU
      b1.isOccupied = 0 and  // Release previous bed
      b1.assignedPatient = none and  // No longer assigned to any patient
      b2.isOccupied = 1 and  // The new bed must be occupied
      b2.assignedPatient = p // The patient is assigned to the new bed
    }
}
check BedReleaseWhenPatientTransferredAndBedTypeAssertion for 5

// 7. For pharmacy dispatch, both the prescription ID and the patient ID must match.
fact PharmacyDispatchPrescriptionIDMatch {
  all p: Prescription |
    p.appointment.patient.id = p.appointment.patient.id // prescription is matched to the correct patient.
}

// Assertion to verify that prescriptions are correctly matched to patients
assert PharmacyDispatchPrescriptionIDMatchAssertion {
  all p: Prescription |
    p.appointment.patient.id = p.appointment.patient.id and
    p.id != none // Ensure prescription has an ID
}
check PharmacyDispatchPrescriptionIDMatchAssertion for 5

// 8. Lab tests can only be ordered if the patient has an active appointment or is admitted, and the test is requested by a registered doctor.
fact LabTestOrderConditions {
  all lt: LabTest |
    (lt.appointment.status = "Active" or lt.appointment.patient.appointment != none) and // Admitted = has a bed.
    lt.appointment.doctor in Doctor // Ensure that lab tests are ordered only by registered doctors.
}

// Assertion for LabTestOrderConditions
assert LabTestOrderConditionsAssertion {
  all lt: LabTest |
    (lt.appointment.status = "Active" or lt.appointment.patient.appointment != none) and
    lt.appointment.doctor in Doctor
}
check LabTestOrderConditionsAssertion for 5

// 9. If the patient's history includes an allergy, medicine containing allergens must be blocked from prescription.
fact BlockAllergenMedicineFromPrescription {
  all p: Patient, m: Medicine |
    some a: p.ehr.allergies | 
    a.name in m.allergens implies 
    not (m in p.prescription.medicines)
}

// Assertion to verify that medicines containing allergens are blocked from prescription
assert BlockAllergenMedicineFromPrescriptionAssertion {
  all p: Patient, m: Medicine |
    some a: p.ehr.allergies | 
    a.name in m.allergens implies 
    not (m in p.prescription.medicines)
}
check BlockAllergenMedicineFromPrescriptionAssertion for 5

// 10. Operation theater, surgeon, and anesthetist must be available at the time of surgery.
fact OperationTheaterAndStaffAvailability {
  all s: Surgery |
    // Basic availability checks
    some ot: OperationTheater | ot.id = s.assignedOT and
    some surgeon: Doctor | surgeon = s.appointment.doctor and
    some an: Staff | an = s.anesthetist and
    
    // Simplified time slot checks
    some surgeonShift: surgeon.assignedShifts |
      surgeonShift.date = s.appointment.date and
      timeInMinutes[s.appointment.timeSlot.startingTime] >= timeInMinutes[surgeonShift.startingTime] and
      timeInMinutes[s.appointment.timeSlot.endingTime] <= timeInMinutes[surgeonShift.endingTime]
}

// Assertion with simplified constraints
assert OperationTheaterAndStaffAvailabilityAssertion {
  all s: Surgery |
    // Basic availability checks
    some ot: OperationTheater | ot.id = s.assignedOT and
    some surgeon: Doctor | surgeon = s.appointment.doctor and
    some an: Staff | an = s.anesthetist and
    
    // Simplified time slot checks
    some surgeonShift: surgeon.assignedShifts |
      surgeonShift.date = s.appointment.date and
      timeInMinutes[s.appointment.timeSlot.startingTime] >= timeInMinutes[surgeonShift.startingTime] and
      timeInMinutes[s.appointment.timeSlot.endingTime] <= timeInMinutes[surgeonShift.endingTime]
}
check OperationTheaterAndStaffAvailabilityAssertion for 5

//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Business or Real World Rules (5 - 10)>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

//1. Appointments cannot be scheduled on national holidays except in emergencies.
fact NoAppointmentOnNationalHolidaysExceptEmergency{
   all a: Appointment | a.date in NationalHolidays.dates implies a.type = "Emergency"
}

// Assertion.
assert NoAppointmentOnNationalHolidaysExceptEmergencyAssertion {
  all a: Appointment |
    a.date in NationalHolidays.dates implies a.type = "Emergency"
}
check NoAppointmentOnNationalHolidaysExceptEmergencyAssertion for 5

//2. ICU patients must have 24/7 nursing.
fact ICUPatientsHaveNursing24_7{
  all p: Patient |
    p.bed != none and p.bed.type = "ICU" implies
      some s1, s2, s3: Shift, n1, n2, n3: Staff |
        n1.type = "Nurse" and n1 in s1.assignedTo and
        n2.type = "Nurse" and n2 in s2.assignedTo and
        n3.type = "Nurse" and n3 in s3.assignedTo
}

assert ICUPatientsHaveNursing24_7Assertion {
  all p: Patient |
    p.bed != none and p.bed.type = "ICU" implies
      some s1, s2, s3: Shift, n1, n2, n3: Staff |
        n1.type = "Nurse" and n1 in s1.assignedTo and
        n2.type = "Nurse" and n2 in s2.assignedTo and
        n3.type = "Nurse" and n3 in s3.assignedTo
}

check ICUPatientsHaveNursing24_7Assertion for 5

// 3. A discharge summary must be reviewed and signed by a senior doctor.
fact DischargeSummaryReviewdAndSignedBySeniorDoctor {
  all ds: DischargeSummary |
    ds.signedBy.rank = "Senior"
}

// Assertion to verify that all discharge summaries are signed by senior doctors
assert DischargeSummarySignedBySeniorDoctorAssertion {
  all ds: DischargeSummary |
    ds.signedBy.rank = "Senior"
}
check DischargeSummarySignedBySeniorDoctorAssertion for 5

//4. Emergency appointments override schedules.
fact EmergencyAppointmentsOverRideScdedules {
  all a1, a2: Appointment |
    a1 != a2 and 
    a1.date = a2.date and 
    a1.timeSlot = a2.timeSlot and 
    a1.doctor = a2.doctor and
    a1.type != "Emergency" and
    a2.type != "Emergency" =>
      a1.status = "Cancelled" or a2.status = "Cancelled"
}

// Assertion for Emergency appointments overriding schedules
assert EmergencyAppointmentsOverRideScdedulesAssertion {
  all a1, a2: Appointment |
    a1 != a2 and 
    a1.date = a2.date and 
    a1.timeSlot = a2.timeSlot and 
    a1.doctor = a2.doctor and
    a1.type != "Emergency" and
    a2.type != "Emergency" =>
      a1.status = "Cancelled" or a2.status = "Cancelled"
}
check EmergencyAppointmentsOverRideScdedulesAssertion for 5


//5. Poor feedback triggers a review.
fact PoorFeedbackTriggersReview {
   all f: Feedback |
    f.rating < 3 => {
      some qa: Staff | qa.type = "QualityAssuranceTeam" and qa in f.notifiedTeam
    }
}

// Assertion for Poor feedback triggering review
assert PoorFeedbackTriggersReviewAssertion {
  all f: Feedback |
    f.rating < 3 => {
      some qa: Staff | qa.type = "QualityAssuranceTeam" and qa in f.notifiedTeam
    }
}
check PoorFeedbackTriggersReviewAssertion for 5

//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< Assertion to Verify >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

// 1. All patients must have at least one EHR entry.
fact AtleastOneEHREntry {
  all p: Patient |
    some ehr: EHR | ehr.patient = p
}

// Assertion for AtleastOneEHREntry
assert AtleastOneEHREntryAssertion {
  all p: Patient |
    some ehr: EHR | ehr.patient = p
}
check AtleastOneEHREntryAssertion for 5

// All bills must match the sum of resources, lab tests, and medication costs.
fact BillMatchTheSum {
  all b: Bill | 
    let a = b.appointment |
    let total_Resources_Cost = sum r: a.resources | r.resourceCost |
    let total_LabTests_Cost = sum l: a.labTests | l.testCost |
    let total_Medicines_Cost = sum m: { m: Medicine | some pr: b.appointment.patient.prescription 
      | pr.appointment = a and m in pr.medicines } | m.medicineCost |
    b.totalAmount = total_Resources_Cost + total_LabTests_Cost + total_Medicines_Cost
}

// Assertion for BillMatchTheSum
assert BillMatchTheSumAssertion {
  all b: Bill | 
    let a = b.appointment |
    let total_Resources_Cost = sum r: a.resources | r.resourceCost |
    let total_LabTests_Cost = sum l: a.labTests | l.testCost |
    let total_Medicines_Cost = sum m: { m: Medicine | some pr: b.appointment.patient.prescription 
      | pr.appointment = a and m in pr.medicines } | m.medicineCost |
    b.totalAmount = total_Resources_Cost + total_LabTests_Cost + total_Medicines_Cost
}
check BillMatchTheSumAssertion for 5

// Meds can’t be issued without a prescription.
fact MedsCannotBeIssuedWithoutPrescription {
  all m: Medicine |
    some p: Prescription | p.medicines = m => some p
}

// Assertion for MedsCannotBeIssuedWithoutPrescription
assert MedsCannotBeIssuedWithoutPrescriptionAssertion {
  all m: Medicine |
    some p: Prescription | p.medicines = m => some p
}
check MedsCannotBeIssuedWithoutPrescriptionAssertion for 5


// Feedback must be linked to completed appointments.
fact FeedbackLinkedToCompletedAppointments {
  all f: Feedback |
    f.appointment.status = "Completed" and f.appointment = f.appointment
}

// Assertion for FeedbackLinkedToCompletedAppointments
assert FeedbackLinkedToCompletedAppointmentsAssertion {
  all f: Feedback |
    f.appointment.status = "Completed" and f.appointment = f.appointment
}
check FeedbackLinkedToCompletedAppointmentsAssertion for 5

// A resource must be available before it can be booked.
fact ResourceAvailabilityBeforeBooking {
  all r: Resource |
    r.isAvailable = 1 => some a: Appointment | a.resources = r
}

// Assertion for ResourceAvailabilityBeforeBooking
assert ResourceAvailabilityBeforeBookingAssertion {
  all r: Resource |
    r.isAvailable = 1 => some a: Appointment | a.resources = r
}
check ResourceAvailabilityBeforeBookingAssertion for 5






//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< SCENARIOS >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

// Scenario 1: Check bed transfer and ICU nursing assignment together
assert BedTransferAndICUNursing {
  all p: Patient, b1, b2: Bed |
    p.bed = b1 and b2.isOccupied = 0 and
    p.bed = b2 implies {
      // Bed transfer conditions
      b1.type = "General Ward" and
      b2.type = "ICU" and
      b1.isOccupied = 0 and
      b1.assignedPatient = none and
      b2.isOccupied = 1 and
      b2.assignedPatient = p and
      // ICU nursing conditions
      some n: Staff |
        n.type = "Nurse" and
        some s: n.assignedShifts |
          s.date = p.appointment.date and
          s.location = "ICU"
    }
}

// Scenario 2: Check appointment scheduling with doctor availability and working hours
assert AppointmentSchedulingConstraints {
  all a: Appointment |
    // Doctor must be available
    some s: a.doctor.assignedShifts | s.date = a.date and
    // Appointment must be within working hours
    timeInMinutes[a.timeSlot.startingTime] >= timeInMinutes[s.startingTime] and
    timeInMinutes[a.timeSlot.endingTime] <= timeInMinutes[s.endingTime] and
    // No overlapping appointments
    all a2: Appointment |
      a2 != a and a2.doctor = a.doctor and a2.date = a.date implies
        timeInMinutes[a.timeSlot.endingTime] <= timeInMinutes[a2.timeSlot.startingTime] or
        timeInMinutes[a2.timeSlot.endingTime] <= timeInMinutes[a.timeSlot.startingTime]
}

// Scenario 3: Check prescription and allergy safety together
assert PrescriptionAndAllergySafety {
  all p: Patient, m: Medicine |
    // If medicine is prescribed
    m in p.prescription.medicines implies {
      // Must have valid prescription
      some pr: Prescription | pr.medicines = m and pr.appointment.patient = p and
      // Must not contain allergens
      no a: p.ehr.allergies | a.name in m.allergens
    }
}

// Scenario 4: Check surgery scheduling with staff and resource availability
assert SurgeryScheduling {
  all s: Surgery |
    // Operation theater must be available
    some ot: OperationTheater | ot.id = s.assignedOT and
    // Surgeon must be available
    some surgeon: Doctor | surgeon = s.appointment.doctor and
    // Anesthetist must be available
    some an: Staff | an = s.anesthetist and
    // Check staff availability during surgery time
    some surgeonShift: surgeon.assignedShifts |
      surgeonShift.date = s.appointment.date and
      timeInMinutes[s.appointment.timeSlot.startingTime] >= timeInMinutes[surgeonShift.startingTime] and
      timeInMinutes[s.appointment.timeSlot.endingTime] <= timeInMinutes[surgeonShift.endingTime]
}

// Scenario 5: Check billing and treatment relationship
assert BillingAndTreatment {
  all p: Patient |
    p.ehr.receivedtreatment = 1 implies {
      some b: Bill | 
        b.appointment.patient = p and
        let totalResources = sum r: b.appointment.resources | r.resourceCost,
            totalLabTests = sum l: b.appointment.labTests | l.testCost,
            totalMedicines = sum m: { m: Medicine | some pr: p.prescription | 
              pr.appointment = b.appointment and m in pr.medicines } | m.medicineCost |
        b.totalAmount = totalResources + totalLabTests + totalMedicines
    }
}


// Scenario 6: Complete Emergency Management
// assert ComprehensiveEmergencyManagement {
//   all e: Emergency |
//     // Emergency must have valid patient
//     some p: Patient | p = e.patient and {
//       // Emergency must be handled by available staff
//       some d: Doctor | d = e.attendingDoctor and d.isOnLeave = 0 and
//       some n: Staff | n.type = "Nurse" and n in e.assignedNurses and n.isOnLeave = 0 and
      
//       // Emergency must have required resources
//       all r: e.requiredResources | {
//         r.isAvailable = 1 and
//         (r.type = "Emergency Equipment" or r.type = "Life Support Equipment") and
//         r.lastMaintenanceDate != none and
        
//         // Resources must be in emergency department
//         some ed: EmergencyDepartment | r in ed.resources and
//           ed.isOperational = 1
//       }
//     }
// }

// // Scenario 7: Complete Laboratory Management
// assert ComprehensiveLaboratoryManagement {
//   all l: LabTest |
//     // Test must be ordered by valid doctor
//     some d: Doctor | d = l.orderedBy and d.isOnLeave = 0 and {
//       // Test must be for valid patient
//       some p: Patient | p = l.patient and {
//         // Test must be performed in operational lab
//         some lab: Laboratory |
//           lab.isOperational = 1 and
//           lab.type = l.testType and
//           // Lab must have required equipment
//           some e: Equipment | e in lab.equipment and
//             e.type = l.requiredEquipment and
//             e.isAvailable = 1 and
//             e.lastCalibrationDate != none
//       } and
        
//       // Results must be properly documented
//       l.result != none => {
//         l.resultDate != none and
//         some t: Staff | t.type = "LabTechnician" and t in l.performedBy
//       }
//     }
// }

// // Scenario 8: Complete Staff Management
// // assert ComprehensiveStaffManagement {
// //   all s: Staff |
// //     // Basic staff requirements
// //     s.id != none and
// //     s.name != none and
// //     s.qualification != none and
    
// //     // If staff is on leave
// //     (s.isOnLeave = 1 => {
// //       // Staff on leave should not be assigned to any shifts on that day
// //       no sh: s.assignedShifts
// //     }) and
    
// //     // If staff is assigned shifts
// //     (some sh: s.assignedShifts => {
// //       // No overlapping shifts
// //       all sh1, sh2: s.assignedShifts |
// //         sh1 != sh2 and sh1.date = sh2.date => {
// //           timeInMinutes[sh1.endingTime] <= timeInMinutes[sh2.startingTime] or
// //           timeInMinutes[sh2.endingTime] <= timeInMinutes[sh1.startingTime]
// //         }
// //     })
// // }





// // Scenario 9: Complete Resource Inventory Management
// assert ComprehensiveResourceManagement {
//   all r: Resource |
//     // Basic resource requirements
//     r.id != none and
//     r.type != none and
//     (r.isAvailable = 0 or r.isAvailable = 1) and
    
//     // If resource is assigned
//     some a: Appointment | a.resources = r => {
//       // Resource must be available
//       r.isAvailable = 1 and
//       // Resource must be properly maintained
//       r.lastMaintenanceDate != none and
//       r.nextMaintenanceDate != none and
//       // Resource must be in correct location
//       some l: Location | r in l.resources and
//         l.type = r.requiredLocation
//     } and
    
//     // Maintenance requirements
//     r.lastMaintenanceDate != none => {
//       some m: Maintenance | m.resource = r and
//         m.date = r.lastMaintenanceDate and
//         m.performedBy != none and
//         m.status = "Completed"
//     }
// }

// // Scenario 10: Complete Patient Record Management
// assert ComprehensivePatientRecordManagement {
//   all p: Patient |
//     // Basic patient information
//     p.id != none and
//     p.name != none and
//     p.dob != none and
    
//     // Must have EHR
//     some e: EHR | e.patient = p and {
//       // EHR must be properly maintained
//       e.lastUpdated != none and
//       e.updatedBy != none and
      
//       // Allergies check
//       all a: e.allergies | {
//         a.name != none and
//         a.severity != none and
//         a.diagnosedDate != none
//       } and
      
//       // Medications check
//       all m: e.medications | {
//         m.name != none and
//         m.dosage != none and
//         m.frequency != none
//       }
//     }
// }

// // Check all assertions
check BedTransferAndICUNursing
check AppointmentSchedulingConstraints
check PrescriptionAndAllergySafety
check SurgeryScheduling
check BillingAndTreatment
// check ComprehensiveEmergencyManagement for 5
// check ComprehensiveLaboratoryManagement for 5
// check ComprehensiveStaffManagement for 5
// check ComprehensiveResourceManagement for 5
// check ComprehensivePatientRecordManagement for 5